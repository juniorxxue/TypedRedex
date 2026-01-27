# TypedRedex Outline

A VS Code extension that shows the outline of TypedRedex DSL judgments defined in `Rules.hs` files.

## Features

- Displays judgment names with their modes (I/O) and types in the VS Code Outline view
- Automatically activates when opening files named `Rules.hs`
- Shows each judgment in the format: `judgmentName` with detail `I:Type1, O:Type2, ...`

## Example

For a judgment definition like:
```haskell
lookupTmVar :: Judgment "lookupVar" '[I, I, O] '[Env, Nom, Ty]
```

The outline will show:
- **lookupVar** — `I:Env, I:Nom, O:Ty`

## Installation

1. Open the extension folder in VS Code
2. Run `npm install` to install dependencies
3. Run `npm run compile` to compile the TypeScript
4. Press `F5` to run the extension in a new Extension Development Host window

## Usage

1. Open a `Rules.hs` file containing TypedRedex judgment definitions
2. Open the Outline view (View → Outline or click the Outline section in the Explorer sidebar)
3. You'll see all the judgment definitions listed with their modes and types

## Building for Distribution

```bash
npm install -g @vscode/vsce
vsce package
```

This will create a `.vsix` file that can be installed in VS Code.
