import * as vscode from 'vscode';

/**
 * Represents a parsed TypedRedex judgment definition
 */
interface JudgmentInfo {
    name: string;           // The variable name (e.g., "flipPolar")
    judgmentName: string;   // The judgment name in quotes (e.g., "flipPolar")
    modes: string[];        // The modes (I/O)
    types: string[];        // The types
    line: number;           // Line number in the document
    range: vscode.Range;    // Full range of the declaration
}

/**
 * Parse a TypedRedex Rules.hs file to extract judgment definitions
 */
function parseJudgments(document: vscode.TextDocument): JudgmentInfo[] {
    const judgments: JudgmentInfo[] = [];
    const text = document.getText();
    const lines = text.split('\n');

    // Pattern to match judgment type signatures like:
    // flipPolar :: Judgment "flipPolar" '[I, O] '[Polar, Polar]
    // lookupTmVar :: Judgment "lookupVar" '[I, I, O] '[Env, Nom, Ty]
    const judgmentPattern = /^(\w+)\s*::\s*Judgment\s+"([^"]+)"\s+'\[([^\]]*)\]\s+'\[([^\]]*)\]/;

    for (let i = 0; i < lines.length; i++) {
        const line = lines[i];
        const match = line.match(judgmentPattern);

        if (match) {
            const [, varName, judgmentName, modesStr, typesStr] = match;

            // Parse modes (e.g., "I, O" -> ["I", "O"])
            const modes = modesStr.split(',').map(m => m.trim()).filter(m => m.length > 0);

            // Parse types (e.g., "Polar, Polar" -> ["Polar", "Polar"])
            const types = typesStr.split(',').map(t => t.trim()).filter(t => t.length > 0);

            const startPos = new vscode.Position(i, 0);
            const endPos = new vscode.Position(i, line.length);

            judgments.push({
                name: varName,
                judgmentName: judgmentName,
                modes: modes,
                types: types,
                line: i,
                range: new vscode.Range(startPos, endPos)
            });
        }
    }

    return judgments;
}

/**
 * Format mode and type information for display
 */
function formatModeType(modes: string[], types: string[]): string {
    if (modes.length !== types.length) {
        return `[${modes.join(', ')}] : [${types.join(', ')}]`;
    }

    // Combine modes and types: e.g., "I:Env, I:Nom, O:Ty"
    const combined = modes.map((mode, idx) => `${mode}:${types[idx]}`);
    return combined.join(', ');
}

/**
 * DocumentSymbolProvider for TypedRedex DSL
 */
class TypedRedexDocumentSymbolProvider implements vscode.DocumentSymbolProvider {
    provideDocumentSymbols(
        document: vscode.TextDocument,
        token: vscode.CancellationToken
    ): vscode.ProviderResult<vscode.DocumentSymbol[]> {
        // Only process files named "Rules.hs"
        if (!document.fileName.endsWith('Rules.hs')) {
            return [];
        }

        const judgments = parseJudgments(document);
        const symbols: vscode.DocumentSymbol[] = [];

        for (const judgment of judgments) {
            // Create the detail string showing modes and types
            const detail = formatModeType(judgment.modes, judgment.types);

            // Create the display name
            const displayName = `${judgment.judgmentName}`;

            const symbol = new vscode.DocumentSymbol(
                displayName,
                detail,
                vscode.SymbolKind.Function,
                judgment.range,
                judgment.range
            );

            symbols.push(symbol);
        }

        return symbols;
    }
}

/**
 * Activate the extension
 */
export function activate(context: vscode.ExtensionContext) {
    console.log('TypedRedex Outline extension is now active');

    // Register the document symbol provider for Haskell files
    const symbolProvider = vscode.languages.registerDocumentSymbolProvider(
        { language: 'haskell' },
        new TypedRedexDocumentSymbolProvider()
    );

    context.subscriptions.push(symbolProvider);
}

/**
 * Deactivate the extension
 */
export function deactivate() {}
