using Cysharp.Text;
using Shared;

namespace CSharpHelpers;

public static class FileManagerHelper
{
    // need thread-safe
    public static string ConvertPathToLogicalPath(
        ReadOnlySpan<char> path,
        IEnumerable<ExpandedWorkspaceDirectory> expandedWorkspaceDirectories,
        IEnumerable<string> scriptFolders
    )
    {
        // must be false
        using var sb = ZString.CreateStringBuilder(false);
        sb.Append(path);
        sb.Replace('\\', '/');

        var pathSpan = sb.AsSpan();
        foreach (var expandedWorkspaceDirectory in expandedWorkspaceDirectories)
        {
            int index = pathSpan.IndexOf(
                expandedWorkspaceDirectory.normalisedPath.AsSpan(),
                StringComparison.Ordinal
            );

            if (index >= 0)
            {
                sb.Remove(0, index + expandedWorkspaceDirectory.normalisedPath.Length);
                pathSpan = sb.AsSpan();
                break;
            }
        }

        if (pathSpan.StartsWith("gfx/", StringComparison.Ordinal))
        {
            return sb.ToString();
        }

        var matches = new List<int>();

        using var pathBuilder = ZString.CreateStringBuilder(false);
        foreach (string folder in scriptFolders)
        {
            int index = FindFolderIndexInPath(pathSpan, folder, pathBuilder);
            if (index < 0)
            {
                continue;
            }

            matches.Add(index);
        }

        var result = sb.ToString();
        if (matches.Count == 0)
        {
            return result;
        }

        int minIndex = matches.Min();
        return result[minIndex..];
    }

    /// <summary>
    /// Returns the index where the folder's relative segment starts in the path
    /// (i.e. just after its leading separator), or -1 if not present.
    /// </summary>
    private static int FindFolderIndexInPath(
        ReadOnlySpan<char> pathSpan,
        string folder,
        Utf16ValueStringBuilder builder
    )
    {
        builder.Clear();

        builder.Append('/');
        builder.Append(folder);
        builder.Append('/');
        builder.Replace('\\', '/');

        var pattern = builder.AsSpan();

        // A path that has already lost its leading separator ("common/...") can never
        // match "/folder/" at position 0; check the separator-less prefix explicitly.
        if (pathSpan.StartsWith(pattern[1..], StringComparison.Ordinal))
        {
            return 0;
        }

        int index = pathSpan.IndexOf(pattern, StringComparison.Ordinal);
        return index < 0 ? index : index + 1;
    }
}
