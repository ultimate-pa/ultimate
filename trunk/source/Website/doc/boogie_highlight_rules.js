define(function(require, exports, module) {

			var oop = require("ace/lib/oop");
			var lang = require("ace/lib/lang");
			var DocCommentHighlightRules = require("ace/mode/doc_comment_highlight_rules").DocCommentHighlightRules;
			var TextHighlightRules = require("ace/mode/text_highlight_rules").TextHighlightRules;

			var BoogieHighlightRules = function() {

				var keywords = lang
						.arrayToMap(("assert|assume|axiom|bool|break|bv0|bv1"
								+ "|bv2|bv3|bv4|bv4|bv5|bv6|bv7|bv8|bv9|call|complete|const|else|ensures|exists|false|finite"
								+ "|forall|free|function|goto|havoc|if|implementation|int"
								+ "|invariant|modifies|old|procedure|requires|return|returns|true"
								+ "|type|unique|var|where|while").split("|"));

				var buildinConstants = lang.arrayToMap(("NULL").split("|"));

				// regexp must not have capturing parentheses. Use (?:) instead.
				// regexps are ordered -> the first match is used

				this.$rules = {
					"start" : [
							{
								token : "comment",
								regex : "\\/\\/.*$"
							},
							new DocCommentHighlightRules()
									.getStartRule("doc-start"),
							{
								token : "comment", // multi line comment
								merge : true,
								regex : "\\/\\*",
								next : "comment"
							},
							{
								token : "string", // single line
								regex : '["](?:(?:\\\\.)|(?:[^"\\\\]))*?["]'
							},
							{
								token : "string", // multi line string start
								merge : true,
								regex : '["].*\\\\$',
								next : "qqstring"
							},
							{
								token : "string", // single line
								regex : "['](?:(?:\\\\.)|(?:[^'\\\\]))*?[']"
							},
							{
								token : "string", // multi line string start
								merge : true,
								regex : "['].*\\\\$",
								next : "qstring"
							},
							{
								token : "constant.numeric", // hex
								regex : "0[xX][0-9a-fA-F]+\\b"
							},
							{
								token : "constant.numeric", // float
								regex : "[+-]?\\d+(?:(?:\\.\\d*)?(?:[eE][+-]?\\d+)?)?\\b"
							},
							{
								token : "constant", // <CONSTANT>
								regex : "<[a-zA-Z0-9.]+>"
							},
							{
								//  token : "keyword", // pre-compiler directivs
								//  regex : "(?:#include|#pragma|#line|#define|#undef|#ifdef|#else|#elif|#endif|#ifndef)"
								//}, {
								token : function(value) {
									//if (value == "this")
									//    return "variable.language";
									/*else*/if (keywords.hasOwnProperty(value))
										return "keyword";
									else if (buildinConstants
											.hasOwnProperty(value))
										return "constant.language";
									else
										return "identifier";
								},
								regex : "[a-zA-Z_$][a-zA-Z0-9_$]*\\b"
							},
							{
								token : "keyword.operator",
								regex : "<==>|==>|\\|\\||&&|!=|<=|>=|<:|<|>|==|\\^|\\+\\+|\\+|\\-|\\*|\\/|%|!|\\:\\:"
							//regex : "!|\\$|%|&|\\*|\\-\\-|\\-|\\+\\+|\\+|~|==|=|!=|<=|>=|<<=|>>=|>>>=|<>|<|>|!|&&|\\|\\||\\?\\:|\\*=|%=|\\+=|\\-=|&=|\\^=|\\b(?:in|new|delete|typeof|void)"
							}, {
								token : "punctuation.operator",
								regex : "\\!|\\-|\\,|\\;"
							}, {
								token : "paren.lparen",
								regex : "[[({]"
							}, {
								token : "paren.rparen",
								regex : "[\\])}]"
							}, {
								token : "text",
								regex : "\\s+"
							} ],
					"comment" : [ {
						token : "comment", // closing comment
						regex : ".*?\\*\\/",
						next : "start"
					}, {
						token : "comment", // comment spanning whole line
						merge : true,
						regex : ".+"
					} ],
					"qqstring" : [ {
						token : "string",
						regex : '(?:(?:\\\\.)|(?:[^"\\\\]))*?"',
						next : "start"
					}, {
						token : "string",
						merge : true,
						regex : '.+'
					} ],
					"qstring" : [ {
						token : "string",
						regex : "(?:(?:\\\\.)|(?:[^'\\\\]))*?'",
						next : "start"
					}, {
						token : "string",
						merge : true,
						regex : '.+'
					} ]
				};

				this.embedRules(DocCommentHighlightRules, "doc-",
						[ new DocCommentHighlightRules().getEndRule("start") ]);
			};

			oop.inherits(BoogieHighlightRules, TextHighlightRules);

			exports.BoogieHighlightRules = BoogieHighlightRules;
		});
