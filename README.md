# cwtools 	![nuget](https://img.shields.io/nuget/v/CWTools.svg)
A library for parsing, editing, and validating Paradox Interactive script files.  
Supports all modern Paradox Interactive games, and targets .net standard 2.0.

Considering contributing? [Start here!](https://github.com/tboby/cwtools/wiki/Contributing)

## Projects that use CW Tools
#### [Stellaris tech tree](http://www.draconas.co.uk/stellaristech): https://github.com/draconas1/stellaris-tech-tree
An interactive tech tree visualiser that uses CW Tools to parse the vanilla tech files, and extract localisation.
#### [SC Mod Manager](https://github.com/WojciechKrysiak/SCModManager): https://github.com/WojciechKrysiak/SCModManager/tree/feature/PortToAvalonia/PDXModLib/Utility
A mod manager that uses CW Tools for parsing and manipulating mod files.

## Example usage (C#)
This is a simple example of loading an event file, modifying it, and printing the updated events.
```csharp
            //Support UTF-8
            Encoding.RegisterProvider(CodePagesEncodingProvider.Instance);

            //Parse event file
            var parsed = CWTools.Parser.CKParser.parseEventFile("./testevent.txt");
            var eventFile = parsed.GetResult();

            //"Process" result into nicer format
            var processed = CK2Process.processEventFile(eventFile);

            //Find interesting event
            var myEvent = processed.Events.FirstOrDefault(x => x.ID == "test.1");
            
            //Add is_triggered_only = true
            var leaf = new Leaf("is_triggered_only", Value.NewBool(true));
            myEvent.AllChildren.Add(Child.NewLeafC(leaf));
            // or
            myEvent.AllChildren.Add(Leaf.Create("is_triggered_only", Value.NewBool(true)));

            //Output
            var output = processed.ToRaw;
            Console.WriteLine(CKPrinter.printKeyValueList(output, 0));
```
Which will take a file like
```
namespace = test

#One event
country_event = {
        id = test.1
    desc = "test description"
}
#Another event
country_event = {
    id = test.2
desc = "test 2 description"
}
```
and output a file like
```
namespace = test
#One event
country_event = {
        is_triggered_only = yes
        id = test.1
        desc = "test description"
         }
#Another event
country_event = {
        id = test.2
        desc = "test 2 description"
         }
```

## Integration with cwtools-vscode

This repository is included by
[`cwtools-vscode`](https://github.com/Aa728848/cwtools-vscode) as the
`submodules/cwtools` Git submodule. In that parent project it owns the reusable
F# semantics used by `src/Main`, including parsing, validation, game models,
shader support, and scripted-type discovery and refresh.

### Change boundary

- Put reusable parser, validator, game-model, shader, or scripted-type semantics
  in this repository.
- Keep VS Code Extension Host, Webview, AI runner, MCP adapter, and packaging
  changes in the parent `cwtools-vscode` repository.
- Keep Stellaris `.cwt` rules in the sibling
  `submodules/cwtools-stellaris-config` repository.
- Avoid adding behavior that is specific to the downstream extension unless it
  is expressed as a reusable library capability.

### Development and verification

Clone the parent repository with `--recurse-submodules`, or initialize this
checkout with `git submodule update --init --recursive`. For a library change,
run the narrowest relevant CWTools tests and build this solution. Then, from the
parent repository root, verify the downstream server integration:

```bash
dotnet build submodules/cwtools/cwtools.slnx
dotnet build src/Main/
```

Incremental scripted-type refresh has limited upstream test coverage. Changes
to that path should compare incremental results with a full refresh, including
definition additions, edits, and removals.

Commit changes inside this submodule first. Then return to the parent repository
and commit the updated submodule pointer separately. Do not combine library
semantics and rules-data updates in one undifferentiated commit.

## 与 cwtools-vscode 的集成

本仓库作为 `submodules/cwtools` Git 子模块集成到
[`cwtools-vscode`](https://github.com/Aa728848/cwtools-vscode) 中。在父项目中，
它负责 `src/Main` 复用的 F# 语义能力，包括解析、校验、游戏模型、Shader
支持，以及 scripted type 的发现和刷新。

### 修改边界

- 可复用的解析器、校验器、游戏模型、Shader 或 scripted type 语义应放在本仓库。
- VS Code Extension Host、Webview、AI runner、MCP 适配器和打包逻辑应留在父仓库。
- Stellaris `.cwt` 规则应放在相邻的
  `submodules/cwtools-stellaris-config` 仓库。
- 除非能抽象为可复用库能力，否则不要加入只服务于下游扩展的专用行为。

### 开发与验证

克隆父仓库时使用 `--recurse-submodules`，或执行
`git submodule update --init --recursive` 初始化本仓库。修改库代码后，先运行
范围最小的相关 CWTools 测试并构建本解决方案，再回到父仓库根目录验证服务端集成：

```bash
dotnet build submodules/cwtools/cwtools.slnx
dotnet build src/Main/
```

scripted type 增量刷新缺少充分的上游测试覆盖。修改该路径时，应分别验证定义的
新增、修改和删除，并对比增量刷新与全量刷新的结果。

请先在本子模块内部提交，再回到父仓库单独提交更新后的 submodule 指针。不要把库
语义修改和规则数据更新混在一个无法区分职责的提交中。
