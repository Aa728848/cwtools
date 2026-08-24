#![forbid(unsafe_code)]
use cwtools_workspace::{
    DiscoveryOptions, Overwrite, Resource, ResourceKind, ResourceSnapshot, TextEncoding, discover,
    discover_zip,
};
use serde::{Deserialize, Serialize};
use std::io::{self, Read};
use std::path::PathBuf;

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct WorkspaceRoot {
    path: String,
    scope: String,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct ZipInput {
    path: String,
    scope: String,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Request {
    root: String,
    scope: String,
    #[serde(default)]
    roots: Vec<WorkspaceRoot>,
    #[serde(default)]
    zips: Vec<ZipInput>,
    script_folders: Vec<String>,
    max_files: usize,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct FileProjection {
    kind: &'static str,
    scope: String,
    path: String,
    logical_path: String,
    validate: bool,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct OverwriteProjection {
    path: String,
    logical_path: String,
    overwrite: &'static str,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct Projection {
    schema_version: &'static str,
    implementation: &'static str,
    files: Vec<FileProjection>,
    overwrite: Vec<OverwriteProjection>,
}

#[allow(clippy::too_many_lines)]
fn run() -> Result<Projection, String> {
    let mut input = String::new();
    io::stdin()
        .read_to_string(&mut input)
        .map_err(|error| error.to_string())?;
    let request: Request = serde_json::from_str(&input).map_err(|error| error.to_string())?;
    if request.root.trim().is_empty() {
        return Err("root is required".into());
    }
    let script_folders = request.script_folders;
    let roots = if request.roots.is_empty() {
        vec![WorkspaceRoot {
            path: request.root,
            scope: request.scope,
        }]
    } else {
        request.roots
    };
    let mut discovered = Vec::new();
    for root in roots {
        let mut options =
            DiscoveryOptions::bounded(PathBuf::from(root.path), root.scope, script_folders.clone());
        options.max_files = request.max_files.saturating_sub(discovered.len());
        options.max_file_size_mb = 64;
        discovered.extend(discover(&options).map_err(|error| error.to_string())?);
        if discovered.len() > request.max_files {
            return Err(format!(
                "workspace exceeds {} discovered files",
                request.max_files
            ));
        }
    }
    for zip in request.zips {
        let resources = discover_zip(
            PathBuf::from(zip.path).as_path(),
            &zip.scope,
            &script_folders,
            TextEncoding::Utf8,
            64,
        )
        .map_err(|error| error.to_string())?;
        if discovered.len().saturating_add(resources.len()) > request.max_files {
            return Err(format!(
                "workspace exceeds {} discovered files",
                request.max_files
            ));
        }
        discovered.extend(resources.into_iter().map(|resource| {
            cwtools_workspace::DiscoveredFile {
                scope: resource.scope,
                path: PathBuf::from(resource.uri),
                logical_path: resource.logical_path,
                length: resource.text.as_ref().map_or(0, String::len) as u64,
                admission: resource.admission,
            }
        }));
    }
    let mut files = discovered
        .into_iter()
        .filter(|file| {
            script_folders.iter().any(|folder| {
                file.logical_path == *folder
                    || file
                        .logical_path
                        .strip_prefix(folder)
                        .is_some_and(|suffix| suffix.starts_with('/'))
            })
        })
        .map(|file| FileProjection {
            kind: match file.admission.kind {
                ResourceKind::Entity => "entity",
                ResourceKind::Content => "content",
                ResourceKind::File => "file",
            },
            scope: file.scope,
            path: file.path.to_string_lossy().replace('\\', "/"),
            logical_path: file.logical_path,
            validate: file.admission.validate,
        })
        .collect::<Vec<_>>();
    let mut overwrite = ResourceSnapshot::build(
        files
            .iter()
            .filter(|file| file.kind == "entity")
            .map(|file| Resource {
                scope: file.scope.clone(),
                file_path: file.path.clone(),
                logical_path: file.logical_path.clone(),
                value: (),
                overwrite: Overwrite::No,
                validate: file.validate,
            })
            .collect(),
    )
    .resources()
    .iter()
    .map(|resource| OverwriteProjection {
        path: resource.file_path.clone(),
        logical_path: resource.logical_path.clone(),
        overwrite: match resource.overwrite {
            Overwrite::No => "none",
            Overwrite::Overwrote => "overwrote",
            Overwrite::Overwritten => "overwritten",
        },
    })
    .collect::<Vec<_>>();
    overwrite.sort_by(|left, right| {
        (&left.logical_path, &left.path).cmp(&(&right.logical_path, &right.path))
    });
    files.sort_by(|left, right| {
        (&left.logical_path, &left.path, left.kind).cmp(&(
            &right.logical_path,
            &right.path,
            right.kind,
        ))
    });
    Ok(Projection {
        schema_version: "cwtools.workspace-projection/v1",
        implementation: "rust",
        files,
        overwrite,
    })
}

fn main() {
    match run() {
        Ok(projection) => println!(
            "{}",
            serde_json::to_string(&projection).expect("serialize projection")
        ),
        Err(error) => {
            println!(
                "{}",
                serde_json::json!({
                    "schemaVersion": "cwtools.workspace-projection/v1",
                    "implementation": "rust",
                    "error": error,
                })
            );
            std::process::exit(1);
        }
    }
}
