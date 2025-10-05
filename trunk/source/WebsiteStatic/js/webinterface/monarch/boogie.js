// Syntax highlighting for the Boogie intermediate verification language dialect used by Ultimate.
// Unicode tokens are not supported.
// More details: https://github.com/ultimate-pa/ultimate/wiki/Boogie
// Boogie: https://www.microsoft.com/en-us/research/wp-content/uploads/2016/12/krml178.pdf

function registerBoogieLanguage(monaco) {
  monaco.languages.register({ id: 'boogie' });

  monaco.languages.setMonarchTokensProvider('boogie', {
    keywords: [
      'assert', 'assume', 'axiom', 'break', 'call', 'complete',
      'const', 'else', 'ensures', 'exists', 'false', 'finite', 'forall', 'free', 'function',
      'goto', 'havoc', 'if', 'implementation', 'invariant', 'modifies', 'old',
      'procedure', 'requires', 'return', 'returns', 'true', 'type', 'unique', 'var',
      'where', 'while',

      'struct', 'atomic', 'fork', 'join', // dialect extension
    ],

    typeKeywords: [
      'int', 'bool', 'real', 'bv',
    ],

    operators: [
      '<==>', // EquivOp
      '==>',  // ImplOp
      '||',  // OrOp
      '&&',  // AndOp
      '==', '!=', '<', '>', '<=', '>=', '<:', // RelOp
      '++', // ConcatOp
      '+', '-',  // AddOp
      '*', '/', '%', // MulOp
      '!', // UnOp
      '::', // QSep
    ],

    symbols: /<==>|==>|::|\|\||&&|==|!=|<=|>=|<:|\+\+|[+\-*\/%<>!]/,
    tokenizer: {
      root: [
        { include: '@whitespace' },

        // attributes like {:inline}
        [/\{:/, { token: 'attribute', next: '@attribute' }],

        // numbers
        [/\d*\.\d+([eE][\-+]?\d+)?/, 'number.float'], // maybe supported?
        [/\d+([eE][\-+]?\d+)?/, 'number'],

        // labels
        [/([a-zA-Z_][\w'?]*)(\s*)(:)/, ['identifier', 'white', 'delimiter']],

        // identifiers and keywords
        [/[a-zA-Z_][\w'?]*/, {
          cases: {
            '@keywords': 'keyword',
            '@typeKeywords': 'type',
            '@default': 'identifier',
          },
        }],

        [/[{}()\[\]]/, '@brackets'],
        [/[;,.]/, 'delimiter'],
        [/@symbols/, { cases: { '@operators': 'operator', '@default': '' } }],

        // strings
        [/"([^"\\]|\\.)*$/, 'string.invalid'],
        [/"/, { token: 'string.quote', bracket: '@open', next: '@string' }],
        [/'[^\\']'/, 'string'],
        [/'/, 'string.invalid'],
      ],

      attribute: [
        [/}/, { token: 'attribute', bracket: '@close', next: '@pop' }],

        [/[ \t\r\n]+/, 'white'],
        [/[a-zA-Z_][\w$-]*/, 'constant'],
        [/:/, 'constant'],

        // numbers
        [/\d+\.\d+([eE][\-+]?\d+)?/, 'number.float'],
        [/\d+/, 'number'],

        // strings inside attributes
        [/"/, { token: 'string.quote', bracket: '@open', next: '@attributestring' }],

        // fallback
        [/[^}\s"0-9a-zA-Z:]+/, 'constant'],
      ],

      attributestring: [
        [/[^\\"]+/, 'string'],
        [/\\./, 'string.escape'],
        [/"/, { token: 'string.quote', bracket: '@close', next: '@pop' }],
      ],

      comment: [
        [/[^/*]+/, 'comment'],
        [/\/\*/, 'comment', '@push'],
        [/\*\//, 'comment', '@pop'],
        [/[*\/]/, 'comment'],
      ],

      string: [
        [/[^\\"]+/, 'string'],
        [/"/, { token: 'string.quote', bracket: '@close', next: '@pop' }],
      ],

      whitespace: [
        [/[ \t\r\n]+/, 'white'],
        [/\/\*/, 'comment', '@comment'],
        [/\/\/.*$/, 'comment'],
      ],
    },
  });

  monaco.languages.setLanguageConfiguration('boogie', {
    comments: { lineComment: '//', blockComment: ['/*', '*/'] },
    brackets: [['{', '}'], ['[', ']'], ['(', ')']],
    autoClosingPairs: [
      { open: '{', close: '}' },
      { open: '[', close: ']' },
      { open: '(', close: ')' },
      { open: '"', close: '"', notIn: ['string'] },
      { open: '\'', close: '\'', notIn: ['string', 'comment'] },
    ],
    surroundingPairs: [
      { open: '{', close: '}' },
      { open: '[', close: ']' },
      { open: '(', close: ')' },
      { open: '"', close: '"' },
      { open: '\'', close: '\'' },
    ],
  });
}
