define("ace/mode/automata_script", ["require", "exports", "module", "ace/lib/oop", "ace/mode/text", "ace/tokenizer", "ace/mode/boogie_highlight_rules"], function(a, b, c) {
        var d = a("ace/lib/oop"),
            e = a("ace/mode/text").Mode,
            f = a("ace/tokenizer").Tokenizer,
            g = a("ace/mode/boogie_highlight_rules").BoogieHighlightRules,
            h = function() {
                this.$tokenizer = new f((new g).getRules())
            };
        d.inherits(h, e),
            function() {}.call(h.prototype), b.Mode = h
    }), define("ace/mode/boogie_highlight_rules", ["require", "exports", "module", "ace/lib/oop", "ace/lib/lang", "ace/mode/doc_comment_highlight_rules", "ace/mode/text_highlight_rules"], function(a, b, c) {
        var d = a("ace/lib/oop"),
            e = a("ace/lib/lang"),
            f = a("ace/mode/doc_comment_highlight_rules").DocCommentHighlightRules,
            g = a("ace/mode/text_highlight_rules").TextHighlightRules,
            h = function() {
                var a = e.arrayToMap("assert|FiniteAutomaton|NestedWordAutomaton|Word|LassoWord|NestedLassoWord|NestedWord|print|boolean|bool|break|bv0|bv1|bv2|bv3|bv4|bv4|bv5|bv6|bv7|bv8|bv9|call|complete|const|else|ensures|exists|false|finite|forall|free|function|goto|havoc|if|implementation|int|invariant|modifies|old|procedure|requires|return|returns|true|type|unique|var|where|while".split("|")),
                    b = e.arrayToMap("NULL".split("|"));
                this.$rules = {
                    start: [{
                        token: "comment",
                        regex: "\\/\\/.*$"
                    }, (new f).getStartRule("doc-start"), {
                        token: "comment",
                        merge: !0,
                        regex: "\\/\\*",
                        next: "comment"
                    }, {
                        token: "string",
                        regex: '["](?:(?:\\\\.)|(?:[^"\\\\]))*?["]'
                    }, {
                        token: "string",
                        merge: !0,
                        regex: '["].*\\\\$',
                        next: "qqstring"
                    }, {
                        token: "string",
                        regex: "['](?:(?:\\\\.)|(?:[^'\\\\]))*?[']"
                    }, {
                        token: "string",
                        merge: !0,
                        regex: "['].*\\\\$",
                        next: "qstring"
                    }, {
                        token: "constant.numeric",
                        regex: "0[xX][0-9a-fA-F]+\\b"
                    }, {
                        token: "constant.numeric",
                        regex: "[+-]?\\d+(?:(?:\\.\\d*)?(?:[eE][+-]?\\d+)?)?\\b"
                    }, {
                        token: "constant",
                        regex: "<[a-zA-Z0-9.]+>"
                    }, {
                        token: function(c) {
                            return a.hasOwnProperty(c) ? "keyword" : b.hasOwnProperty(c) ? "constant.language" : "identifier"
                        },
                        regex: "[a-zA-Z_$][a-zA-Z0-9_$]*\\b"
                    }, {
                        token: "keyword.operator",
                        regex: "<==>|==>|\\|\\||&&|!=|<=|>=|<:|<|>|==|\\^|\\+\\+|\\+|\\-|\\*|\\/|%|!|\\:\\:"
                    }, {
                        token: "punctuation.operator",
                        regex: "\\!|\\-|\\,|\\;"
                    }, {
                        token: "paren.lparen",
                        regex: "[[({]"
                    }, {
                        token: "paren.rparen",
                        regex: "[\\])}]"
                    }, {
                        token: "text",
                        regex: "\\s+"
                    }],
                    comment: [{
                        token: "comment",
                        regex: ".*?\\*\\/",
                        next: "start"
                    }, {
                        token: "comment",
                        merge: !0,
                        regex: ".+"
                    }],
                    qqstring: [{
                        token: "string",
                        regex: '(?:(?:\\\\.)|(?:[^"\\\\]))*?"',
                        next: "start"
                    }, {
                        token: "string",
                        merge: !0,
                        regex: ".+"
                    }],
                    qstring: [{
                        token: "string",
                        regex: "(?:(?:\\\\.)|(?:[^'\\\\]))*?'",
                        next: "start"
                    }, {
                        token: "string",
                        merge: !0,
                        regex: ".+"
                    }]
                }, this.embedRules(f, "doc-", [(new f).getEndRule("start")])
            };
        d.inherits(h, g), b.BoogieHighlightRules = h
    }), define("ace/mode/doc_comment_highlight_rules", ["require", "exports", "module", "ace/lib/oop", "ace/mode/text_highlight_rules"], function(a, b, c) {
        "use strict";
        var d = a("../lib/oop"),
            e = a("./text_highlight_rules").TextHighlightRules,
            f = function() {
                this.$rules = {
                    start: [{
                        token: "comment.doc.tag",
                        regex: "@[\\w\\d_]+"
                    }, {
                        token: "comment.doc",
                        merge: !0,
                        regex: "\\s+"
                    }, {
                        token: "comment.doc",
                        merge: !0,
                        regex: "TODO"
                    }, {
                        token: "comment.doc",
                        merge: !0,
                        regex: "[^@\\*]+"
                    }, {
                        token: "comment.doc",
                        merge: !0,
                        regex: "."
                    }]
                }
            };
        d.inherits(f, e),
            function() {
                this.getStartRule = function(a) {
                    return {
                        token: "comment.doc",
                        merge: !0,
                        regex: "\\/\\*(?=\\*)",
                        next: a
                    }
                }, this.getEndRule = function(a) {
                    return {
                        token: "comment.doc",
                        merge: !0,
                        regex: "\\*\\/",
                        next: a
                    }
                }
            }.call(f.prototype), b.DocCommentHighlightRules = f
    }),
    function() {
        window.require(["ace/ace"], function(a) {
            window.ace || (window.ace = {});
            for (var b in a) a.hasOwnProperty(b) && (ace[b] = a[b])
        })
    }()