// Syntax highlighting for automata script
// See: trunk/source/AutomataScriptParser/src/de/uni_freiburg/informatik/ultimate/plugins/source/automatascriptparser/AutomataTestFileLexerSpec.jflex
// Operation names are not highlighted, since they have very similar syntax to functions

function registerAutomataScriptLanguage(monaco) {
  monaco.languages.register({ id: 'automata_script' });

  monaco.languages.setMonarchTokensProvider('automata_script', {
    automataVariants: [
      'NestedWordAutomaton', 'PetriNet', 'EpsilonNestedWordAutomaton', 'FiniteAutomaton', 'RabinAutomaton', 'CountingAutomaton', 'AlternatingAutomaton', 'TreeAutomaton',
    ],

    automataVars: [
      'alphabet', 'callAlphabet', 'internalAlphabet', 'returnAlphabet', 'rankedAlphabet',
      'states', 'initialStates', 'acceptingStates', 'finiteStates', 'finalStates',
      'transitions', 'callTransitions', 'internalTransitions', 'returnTransitions', 'epsilonTransitions',
      'places', 'transitionTable', 'acceptingFunction', 'isReversed', 'counters',
      'initialConditions', 'finalConditions',
      'initialMarking', 'acceptingPlaces',
    ],

    automataTypes: [
      'Word', 'NestedWord', 'LassoWord', 'NestedLassoWord', 'Tree', 'BranchingProcess',
    ],

    tokenizer: {
      root: [
        // whitespace and comments
        { include: '@whitespace' },

        // numbers
        [/\d+/, 'number'],

        // identifiers and keywords
        [/[a-zA-Z_]\w*/, {
          cases: {
            '@automataVariants': 'keyword',
            '@automataVars': 'variable.name',
            '@automataTypes': 'type',
            '@default': 'identifier',
          },
        }],

        // brackets
        [/[{}()\[\]]/, '@brackets'],

        // delimiters
        [/[;,.]/, 'delimiter'],

        // string literal
        [/"/, { token: 'string.quote', bracket: '@open', next: '@string' }],
      ],

      string: [
        [/[^\\"]+/, 'string'],
        [/\\./, 'string.escape.invalid'],
        [/"/, { token: 'string.quote', bracket: '@close', next: '@pop' }],
      ],

      comment: [
        [/[^/*]+/, 'comment'],
        [/\/\*/, 'comment', '@push'],
        [/\*\//, 'comment', '@pop'],
        [/[*\/]/, 'comment'],
      ],

      whitespace: [
        [/[ \t\r\n]+/, 'white'],
        [/\/\*/, 'comment', '@comment'],
        [/\/\/.*$/, 'comment'],
      ],
    },
  });

  monaco.languages.setLanguageConfiguration('automata_script', {
    comments: { lineComment: '//', blockComment: ['/*', '*/'] },
    brackets: [['{', '}'], ['[', ']'], ['(', ')']],
    autoClosingPairs: [
      { open: '{', close: '}' },
      { open: '[', close: ']' },
      { open: '(', close: ')' },
      { open: '"', close: '"', notIn: ['string'] },
    ],
    surroundingPairs: [
      { open: '{', close: '}' },
      { open: '[', close: ']' },
      { open: '(', close: ')' },
      { open: '"', close: '"' },
    ],
  });
}
