define(function(require, exports, module) {

var oop = require("ace/lib/oop");
var TextMode = require("ace/mode/text").Mode;
var Tokenizer = require("ace/tokenizer").Tokenizer;
var BoogieHighlightRules = require("ace/mode/boogie_highlight_rules").BoogieHighlightRules;

var Mode = function() {
    this.$tokenizer = new Tokenizer(new BoogieHighlightRules().getRules());
};
oop.inherits(Mode, TextMode);

(function() {
    // Extra logic goes here. (see below)
}).call(Mode.prototype);

exports.Mode = Mode;
});