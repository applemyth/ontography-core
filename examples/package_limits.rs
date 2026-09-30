//! Measure content-package resolution cost across workspace shapes.
//!
//! `cargo run --release --example package_limits` reruns itself once per case
//! under `/usr/bin/time`, so each peak RSS belongs to that case alone, and
//! prints one markdown row per case. `-- child <build|full> <mem|disk> <shape>`
//! runs a single case: `saves F d N`, `bomb k`, or `wide`. `-- real <dir>`
//! imports a real folder, then opens it under the default limits after 0, 1,
//! 10, 100 and 1,000 one-file saves, timing each open and checking every
//! path, kind, file hash and symlink target against a walk of the filesystem.

#[path = "../tests/support/mod.rs"]
#[allow(dead_code)]
mod support;

use std::collections::{BTreeMap, HashMap};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Arc;
use std::time::{Duration, Instant};

use ontography::content::Hash;
use ontography::package::validate_package_name;
use ontography::{
    ContentId, ContentStore, PackageDocument, PackageLimits, PackageStore, ProposalRuntime,
    ResolvedEntry, ResolvedEntryKind,
};

const UNBOUNDED: PackageLimits = PackageLimits {
    max_documents: usize::MAX,
    max_document_bytes: u64::MAX,
    max_evaluation_bytes: u64::MAX,
    max_entries: usize::MAX,
    max_view_bytes: u64::MAX,
};
const TIMEOUT: Duration = Duration::from_mins(2);

/// A built package, its document count, and the limits it is resolved under.
struct Shape {
    root: ContentId,
    documents: usize,
    limits: PackageLimits,
}

struct Builder {
    content: ContentStore,
    packages: PackageStore,
}

impl Builder {
    async fn put(&self, document: PackageDocument) -> ContentId {
        self.packages.put(&document).await.unwrap()
    }

    async fn file(&self, bytes: impl Into<Vec<u8>>) -> ContentId {
        let content = self.content.import_bytes(bytes.into()).await.unwrap();
        self.put(PackageDocument::File {
            content,
            executable: false,
        })
        .await
    }

    async fn collection(
        &self,
        entries: impl IntoIterator<Item = (String, ContentId)>,
    ) -> ContentId {
        self.put(PackageDocument::Collection {
            entries: entries.into_iter().collect(),
        })
        .await
    }

    async fn build(&self, shape: &[usize]) -> Shape {
        match *shape {
            // F unique files inside d nested folders, then N saves of one file each.
            [0, f, d, n] => {
                let mut files = BTreeMap::new();
                for i in 0..f {
                    files.insert(format!("f{i}"), self.file(format!("file {i}")).await);
                }
                let mut root = self.collection(files).await;
                for _ in 1..d {
                    root = self.collection([("d".into(), root)]).await;
                }
                let folder = "d/".repeat(d - 1);
                for i in 0..n {
                    let file = self.file(format!("save {i}")).await;
                    let changes = BTreeMap::from([(format!("{folder}f{}", i % f), Some(file))]);
                    root = self
                        .put(PackageDocument::Changes {
                            base: root,
                            changes,
                        })
                        .await;
                }
                Shape {
                    root,
                    documents: f + d + 2 * n,
                    limits: UNBOUNDED,
                }
            }
            // k documents whose visible tree doubles at every level.
            [1, k] => {
                let mut root = self.file("bomb").await;
                for _ in 0..k {
                    root = self
                        .collection([("a".into(), root), ("b".into(), root)])
                        .await;
                }
                Shape {
                    root,
                    documents: k + 1,
                    limits: PackageLimits::default(),
                }
            }
            // The largest single collection the default document limit admits.
            [2] => {
                let file = self.file("wide").await;
                let name = |i: usize| format!("{i:0>250}");
                let size = |entries: BTreeMap<String, ContentId>| {
                    serde_json::to_vec(&PackageDocument::Collection { entries })
                        .unwrap()
                        .len()
                };
                let empty = size(BTreeMap::new());
                let entry = size(BTreeMap::from([(name(0), file)])) - empty + 1;
                let n = ((16 << 20) - empty + 1) / entry;
                let root = self.collection((0..n).map(|i| (name(i), file))).await;
                Shape {
                    root,
                    documents: 2,
                    limits: PackageLimits::default(),
                }
            }
            _ => panic!("unknown shape {shape:?}"),
        }
    }
}

fn millis(duration: Duration) -> f64 {
    duration.as_secs_f64() * 1e3
}

/// Build one shape, then time loading and resolving it, printing tab-separated fields.
async fn child(full: bool, disk: bool, shape: &[usize]) {
    let runtime = ProposalRuntime::new(Arc::new(support::kernel(&["A"], &[])));
    let directory = tempfile::tempdir().unwrap();
    let session = if disk {
        runtime.create_persistent(directory.path().join("run"))
    } else {
        runtime.open()
    }
    .unwrap();
    let content = session.content_store().await.unwrap();
    let builder = Builder {
        packages: PackageStore::new(content.clone()).with_limits(UNBOUNDED),
        content: content.clone(),
    };
    let started = Instant::now();
    let shape = builder.build(shape).await;
    let mut fields = vec![
        format!("docs={}", shape.documents),
        format!("build_s={:.1}", started.elapsed().as_secs_f64()),
    ];
    if full {
        std::thread::spawn(|| {
            std::thread::sleep(TIMEOUT);
            println!("outcome=timeout");
            std::process::exit(124);
        });
        let packages = PackageStore::new(content).with_limits(shape.limits);
        let (mut load, mut resolve) = (Duration::MAX, Duration::MAX);
        let mut outcome = String::new();
        for _ in 0..3 {
            let started = Instant::now();
            let loaded = packages.dependencies(shape.root).await;
            load = load.min(started.elapsed());
            let started = Instant::now();
            let resolved = packages.resolve(shape.root).await;
            resolve = resolve.min(started.elapsed());
            outcome = match (loaded, resolved) {
                (_, Ok(view)) => format!("ok, {} entries", view.entry_count()),
                (Err(error), _) | (_, Err(error)) => error.to_string(),
            };
        }
        fields.push(format!("load_ms={:.1}", millis(load)));
        fields.push(format!("resolve_ms={:.1}", millis(resolve)));
        fields.push(format!("outcome={outcome}"));
    }
    println!("{}", fields.join("\t"));
}

/// Folders under `dir` in post-order, so each is built after its children.
fn folders(dir: &Path, out: &mut Vec<PathBuf>) {
    for entry in std::fs::read_dir(dir).unwrap() {
        let entry = entry.unwrap();
        let skipped = matches!(entry.file_name().to_str(), Some(".git" | "target"));
        if entry.file_type().unwrap().is_dir() && !skipped {
            folders(&entry.path(), out);
        }
    }
    out.push(dir.to_owned());
}

/// What the filesystem holds under `dir`, as a view of it should show it: the
/// import's rules, applied by a walk of their own.
fn expected(dir: &Path) -> BTreeMap<String, String> {
    let mut expected = BTreeMap::from([(String::new(), "directory".to_owned())]);
    let mut pending = vec![(dir.to_owned(), String::new())];
    while let Some((folder, prefix)) = pending.pop() {
        for entry in std::fs::read_dir(&folder).unwrap() {
            let entry = entry.unwrap();
            let name = entry.file_name().to_string_lossy().into_owned();
            if validate_package_name(&name).is_err() {
                continue;
            }
            let path = if prefix.is_empty() {
                name.clone()
            } else {
                format!("{prefix}/{name}")
            };
            let kind = entry.file_type().unwrap();
            let fact = if kind.is_symlink() {
                let target = std::fs::read_link(entry.path()).unwrap();
                format!("symlink {}", target.to_string_lossy())
            } else if kind.is_file() {
                format!("file {}", Hash::new(std::fs::read(entry.path()).unwrap()))
            } else if kind.is_dir() && !matches!(name.as_str(), ".git" | "target") {
                pending.push((entry.path(), path.clone()));
                "directory".to_owned()
            } else {
                continue;
            };
            expected.insert(path, fact);
        }
    }
    expected
}

fn fact(entry: &ResolvedEntry) -> String {
    match &entry.kind {
        ResolvedEntryKind::Directory => "directory".to_owned(),
        ResolvedEntryKind::File { content, .. } => format!("file {}", content.hash()),
        ResolvedEntryKind::Symlink { target } => format!("symlink {target}"),
    }
}

/// Import a real folder as one collection per folder, then open it under the
/// default limits as one-file saves accumulate, checking each view against
/// the filesystem.
async fn real(dir: &Path) {
    let session = ProposalRuntime::new(Arc::new(support::kernel(&["A"], &[])))
        .open()
        .unwrap();
    let content = session.content_store().await.unwrap();
    let builder = Builder {
        packages: PackageStore::new(content.clone()).with_limits(UNBOUNDED),
        content: content.clone(),
    };
    let mut order = Vec::new();
    folders(dir, &mut order);
    let (mut ids, mut edited) = (HashMap::new(), None);
    for folder in order {
        let mut entries = BTreeMap::new();
        for entry in std::fs::read_dir(&folder).unwrap() {
            let entry = entry.unwrap();
            let (name, path) = (
                entry.file_name().to_string_lossy().into_owned(),
                entry.path(),
            );
            let kind = entry.file_type().unwrap();
            let id = if validate_package_name(&name).is_err() {
                continue;
            } else if kind.is_symlink() {
                let target = std::fs::read_link(&path)
                    .unwrap()
                    .to_string_lossy()
                    .into_owned();
                builder.put(PackageDocument::Symlink { target }).await
            } else if kind.is_file() {
                edited.get_or_insert_with(|| path.strip_prefix(dir).unwrap().to_owned());
                builder.file(std::fs::read(&path).unwrap()).await
            } else if let Some(id) = ids.remove(&path) {
                id
            } else {
                continue;
            };
            entries.insert(name, id);
        }
        ids.insert(folder, builder.collection(entries).await);
    }
    let edited = edited.unwrap().to_string_lossy().into_owned();
    let mut wanted = expected(dir);
    let packages = PackageStore::new(content);
    let mut root = ids[dir];
    for saves in 0..=1_000 {
        if saves > 0 {
            let last = format!("save {}", saves - 1);
            wanted.insert(edited.clone(), format!("file {}", Hash::new(last)));
        }
        if [0, 1, 10, 100, 1_000].contains(&saves) {
            let started = Instant::now();
            let view = match packages.resolve(root).await {
                Ok(view) => view,
                Err(error) => return println!("saves={saves}\trefused: {error}"),
            };
            let elapsed = millis(started.elapsed());
            let seen: BTreeMap<String, String> = view
                .entries()
                .iter()
                .map(|entry| (entry.path.clone(), fact(entry)))
                .collect();
            println!(
                "saves={saves}\tentries={}\tresolve_ms={elapsed:.1}\tmatches_filesystem={}",
                view.entry_count(),
                seen == wanted
            );
            if let Some(path) = wanted
                .keys()
                .chain(seen.keys())
                .find(|path| wanted.get(*path) != seen.get(*path))
            {
                return println!(
                    "first difference at {path:?}: expected {:?}, saw {:?}",
                    wanted.get(path),
                    seen.get(path)
                );
            }
        }
        let file = builder.file(format!("save {saves}")).await;
        let changes = BTreeMap::from([(edited.clone(), Some(file))]);
        root = builder
            .put(PackageDocument::Changes {
                base: root,
                changes,
            })
            .await;
    }
}

/// Run one child under `/usr/bin/time`, returning its fields and peak RSS in bytes.
fn measure(full: bool, store: &str, shape: &[usize]) -> (BTreeMap<String, String>, u64) {
    let (flag, scale) = if cfg!(target_os = "macos") {
        ("-l", 1)
    } else {
        ("-v", 1024)
    };
    let output = Command::new("/usr/bin/time")
        .arg(flag)
        .arg(std::env::current_exe().unwrap())
        .args(["child", if full { "full" } else { "build" }, store])
        .args(shape.iter().map(ToString::to_string))
        .output()
        .unwrap();
    let stderr = String::from_utf8_lossy(&output.stderr);
    let rss = stderr
        .lines()
        .find(|line| line.contains("aximum resident set size"))
        .and_then(|line| {
            line.split_whitespace()
                .find_map(|word| word.parse::<u64>().ok())
        })
        .map_or(0, |rss| rss * scale);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let fields = stdout
        .lines()
        .flat_map(|line| line.split('\t'))
        .filter_map(|field| field.split_once('='))
        .map(|(key, value)| (key.to_owned(), value.to_owned()))
        .collect();
    (fields, rss)
}

fn cases() -> Vec<(&'static str, &'static str, Vec<usize>)> {
    let mut cases = Vec::new();
    for f in [1_000, 10_000, 100_000] {
        for n in [1, 10, 100, 1_000] {
            cases.push(("saves", "mem", vec![0, f, 1, n]));
        }
    }
    for d in [1, 8, 32, 128] {
        cases.push(("nesting", "mem", vec![0, 10_000, d, 0]));
    }
    for n in [1_000, 10_000, 100_000] {
        cases.push(("depth", "mem", vec![0, 1, 1, n]));
    }
    cases.push(("depth", "disk", vec![0, 1, 1, 10_000]));
    cases.push(("saves", "disk", vec![0, 10_000, 1, 100]));
    for k in [16, 17, 40] {
        cases.push(("bomb", "mem", vec![1, k]));
    }
    cases.push(("wide", "mem", vec![2]));
    cases
}

#[tokio::main]
async fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if let [mode, dir] = args.as_slice()
        && mode == "real"
    {
        return real(Path::new(dir)).await;
    }
    if let [mode, phase, store, shape @ ..] = args.as_slice()
        && mode == "child"
    {
        let shape: Vec<usize> = shape.iter().map(|arg| arg.parse().unwrap()).collect();
        return child(phase == "full", store == "disk", &shape).await;
    }
    println!(
        "| case | store | shape | docs | build s | load ms | resolve ms | evaluate ms | RSS build MiB | RSS full MiB | µs/doc | outcome |"
    );
    println!("|{}", "---|".repeat(12));
    for (name, store, shape) in cases() {
        let (build, build_rss) = measure(false, store, &shape);
        let (full, full_rss) = measure(true, store, &shape);
        let number = |key: &str| {
            full.get(key)
                .and_then(|v| v.parse::<f64>().ok())
                .unwrap_or(0.0)
        };
        let docs: f64 = build["docs"].parse().unwrap();
        println!(
            "| {name} | {store} | {:?} | {docs} | {} | {} | {} | {:.1} | {} | {} | {:.1} | {} |",
            &shape[1..],
            build["build_s"],
            full.get("load_ms").map_or("", String::as_str),
            full.get("resolve_ms").map_or("", String::as_str),
            (number("resolve_ms") - number("load_ms")).max(0.0),
            build_rss >> 20,
            full_rss >> 20,
            number("load_ms") * 1e3 / docs,
            full.get("outcome").map_or("crashed", String::as_str),
        );
    }
}
