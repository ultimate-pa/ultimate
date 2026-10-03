// SMT syntax highlighting
// There are many extensions that add various other keywords. The below definition contains keywords that were somewhere defined or used in Ultimate.

function registerSmtLanguage(monaco) {
  monaco.languages.register({ id: 'smt' });

  monaco.languages.setMonarchTokensProvider('smt', {

    keywords: [
      // Base Theory
      'not', 'and', 'or', '=>', '=', 'distinct', 'xor', 'ite', 'true', 'false', '->',
      // Arithmetic
      '+', '-', '*', '/', 'div', 'mod', 'divisible', 'abs', '>', '>=', '<', '<=', 'to_real', 'to_int', 'is_int',
      // Arrays
      'store', 'select', 'const', '.arrayof',
      // BitVector
      'concat', 'extract', 'bvnot', 'bvand', 'bvor', 'bvneg', 'bvadd', 'bvmul', 'bvudiv', 'bvurem', 'bvshl',
      'bvlshr', 'bvnand', 'bvnor', 'bvxor', 'bvxnor', 'bvcomp', 'bvsub', 'bvsdiv', 'bvsrem', 'bvsmod', 'bvashr', 'repeat',
      'zero_extend', 'sign_extend', 'rotate_left', 'rotate_right', 'bvult', 'bvule', 'bvugt', 'bvuge', 'bvslt', 'bvsle', 'bvsgt', 'bvsge', '#b', '#x',
      'bv2nat', 'nat2bv',
      // Floating Point
      'RoundingMode', 'fp', 'to_fp', 'to_fp_unsigned', 'fp.to_ubv', 'fp.to_sbv', '+oo', '-oo', '+zero', '-zero', 'NaN',
      'roundNearestTiesToEven', 'roundNearestTiesToAway', 'roundTowardsPositive', 'roundTowardsNegative',
      'roundTowardsZero', 'fp.abs', 'fp.neg', 'fp.min', 'fp.max', 'fp.rem', 'fp.add', 'fp.sub', 'fp.mul', 'fp.div', 'fp.fma', 'fp.sqrt',
      'fp.roundToIntegral', 'fp.leq', 'fp.lt', 'fp.geq', 'fp.gt', 'fp.eq', 'fp.isNormal', 'fp.isSubnormal', 'fp.isZero',
      'fp.isInfinite', 'fp.isNaN', 'fp.isNegative', 'fp.isPositive', 'fp.to_real',
      'RNE', 'RNA', 'RTP', 'RTN', 'RTZ',
      // String, Regex
      'String', 'RegLan', 'char', 'str.++', 'str.len', 'str.<', 'str.to_re', 'str.in_re', 're.none', 're.all', 're.allchar',
      're.++', 're.union', 're.inter', 're.*', 'str.<=', 'str.at', 'str.substr', 'str.prefixof', 'str.suffixof', 'str.contains',
      'str.indexof', 'str.replace', 'str.replace_all', 'str.replace_re', 'str.replace_re_all',
      're.comp', 're.diff', 're.+', 're.opt', 're.range', 're.^', 're.loop', 'str.is_digit', 'str.to_code', 'str.from_code', 'str.to_int', 'str.from_int',
      // Command reply
      'error', 'unsupported', 'success', 'sat', 'unknown', 'unsat',

      // Other keywords?
      'intand',
      '@diff', '@0', 'is', '@EQ',

      'benchmark', 'exists', 'flet', 'forall', 'if_then_else', 'iff', 'implies',
      'let', 'logic', 'theory',

      '_', '!', 'as', 'assert', 'check-sat', 'continued-execution', 'DECIMAL',
      'declare-sort', 'declare-fun', 'declare-const', 'declare-datatype', 'declare-datatypes',
      'define-sort', 'define-fun', 'exit', 'get-assertions', 'get-assignment', 'get-info', 'get-interpolants', 'get-model', 'get-option',
      'get-proof', 'get-unsat-core', 'get-unsat-assumptions', 'get-value', 'immediate-exit', 'include',
      'incomplete', 'none', 'NUMERAL', 'match', 'memout', 'par', 'pop', 'push', 'set-logic', 'set-info', 'set-option', 'STRING',
      'simplify', 'reset', 'reset-assertions', 'timed', 'check-allsat', 'echo', 'find-implied-equality', 'check-sat-assuming',
      'stdout', 'stderr',
    ],

    // Colon-prefixed attribute keywords
    colonKeywords: [
      ':named', ':pattern', ':smt-lib-version', ':error-behavior', ':name',
      ':version', ':authors', ':status', ':all-statistics', ':reason-unknown', ':assertion-stack-levels',
      ':diagnostic-output-channel', ':global-declarations', ':interactive-mode', ':print-success', ':produce-assertions',
      ':produce-assignments', ':produce-models', ':produce-proofs', ':produce-unsat-assumptions', ':produce-unsat-cores',
      ':random-seed', ':regular-output-channel', ':reproducible-resource-limit', ':verbosity',

      // More occurrences
      ':logic', ':assumption', ':formula', ':extrasorts', ':extrafuns', ':extrapreds', ':notes', ':pat',

      ':sorts-description', ':sorts', ':funs', ':funs-description', ':definition', ':extensions', ':language', ':theories',
      ':notes', ':values', ':expand-definitions', ':timeout', ':interpolant-check-mode', ':strong-simplifier',
    ],

    // Supported internal sorts
    sortKeywords: [
      'Bool', 'Int', 'Real', 'Array', 'BitVec',
      'FloatingPoint', 'Float16', 'Float32', 'Float64', 'Float128',
    ],

    tokenizer: {
      root: [
        // whitespace
        { include: '@whitespace' },

        // parentheses
        [/\(/, 'delimiter.parenthesis'],
        [/\)/, 'delimiter.parenthesis'],

        // comments
        [/;.*/, 'comment'],

        [/\|/, { token: 'string.source', bracket: '@open', next: '@source' }],

        // numbers
        [/\d+/, 'number'],

        // strings
        [/"/, { token: 'string.quote', bracket: '@open', next: '@string' }],

        // colon keywords
        [/:[a-z\-]+/, {
          cases: {
            '@colonKeywords': 'keyword',
            '@default': 'keyword',
          },
        }],

        // identifiers and keywords
        [/[A-Za-z0-9_.@+\-=><#*\/]+/, {
          cases: {
            '@keywords': 'keyword',
            '@sortKeywords': 'type',
            '@default': 'identifier',
          },
        }],

        // fallback delimiters
        [/[{}[\]]/, '@brackets'],
        [/[;,.]/, 'delimiter'],
      ],

      string: [
        [/""/, 'string'],
        [/[^\\"]+/, 'string'],
        [/"/, { token: 'string.quote', bracket: '@close', next: '@pop' }],
      ],

      source: [
        [/\|/, { token: 'string.source', bracket: '@close', next: '@pop' }],
        [/[^|]+/, 'string.source'],
      ],

      whitespace: [
        [/[ \t\r\n]+/, 'white'],
      ],
    },
  });

  monaco.languages.setLanguageConfiguration('smt', {
    comments: { lineComment: ';' },
    brackets: [['(', ')']],
    autoClosingPairs: [
      { open: '(', close: ')' },
      { open: '"', close: '"' },
      { open: '|', close: '|' },
    ],
    surroundingPairs: [
      { open: '(', close: ')' },
      { open: '"', close: '"' },
      { open: '|', close: '|' },
    ],
  });
}
