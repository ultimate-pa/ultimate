// fetching example asynchronously
function selectExample(ex)
{
  _EDITOR.getSession().setAnnotations([]);
  
  if (!_SPINNER.task.selected) return;

  $.ajax({
      url: _SERVER,
      data: "example=" + encodeURIComponent(ex),
      success: function (json)
      {
         if (json.exampleContent !== null)
         {
           _EDITOR.session.setValue(json.exampleContent);
           _EDITOR.focus();
           return;
         }
       },
      dataType: 'json'
    });
}

function getResults()
{
    _CLEAR = false;
    clearResults();
    
    // get trimmed code from editor
    var trimmedCode = $.trim(_EDITOR.getSession().getValue());
    if (!editorHasCode(trimmedCode))
    {
      toast('No code to ' + _SPINNER.tool.selected.evalText);
      _EDITOR.focus();
      return;
    }
    
    // show ajax-loader on #play
    loading('play', true);
    toast('Fetching Ultimate results...');

    var tc = _SPINNER.task.selected;
    
    var values = "action=execute";
    values += "&code=" + encodeURIComponent(trimmedCode);
    values += getSerializedSettings();
    values += '&taskID='+tc.taskID+'&tcID='+tc.id;

    $.ajax({
        type: "POST",
        url: _SERVER,
        data: values,
        success: function (json) {
            loading('play', false);
            _EDITOR.focus();
            
            if (json.error) { toast("Error:\n\n"+json.error); } else {
                
            if(json.status == "success") { addResults(json.results); }
            else { alert("Unexpected response from server!"); } }
          },
        contentType: 'application/x-www-form-urlencoded;charset=UTF-8',
        dataType: 'json',
        error: function(e) { loading('play', false); toast(e.statusText+' ('+e.status+')'); }
      });
    /*
    var res = [
                {
                  endCol: -1,
                  endLNr: 9,
                  logLvl: "error",
                  longDesc: "Variable is neither declared globally nor locally! ID=lock",
                  shortDesc: "Incorrect Syntax",
                  startCol: -1,
                  startLNr: 7
                },
                {
                    endCol: 10,
                    endLNr: 14,
                    logLvl: "warning",
                    longDesc: "Found wrong description in current line",
                    shortDesc: "Loop invariant",
                    startCol: 3,
                    startLNr: 13
                },
                {
                    endCol: 6,
                    endLNr: 16,
                    logLvl: "info",
                    longDesc: "Have a look on several letters again",
                    shortDesc: "Information found",
                    startCol: 2,
                    startLNr: 12
                },
                {
                    endCol: 6,
                    endLNr: 16,
                    logLvl: "info",
                    longDesc: "Have a look on several letters again",
                    shortDesc: "Information found",
                    startCol: 6,
                    startLNr: 16
                },
                {
                    endCol: -1,
                    endLNr: 56,
                    logLvl: "info",
                    longDesc: "Have a look on several letters again",
                    shortDesc: "Information found",
                    startCol: 0,
                    startLNr: 42
                }
              ];
    setTimeout( function()
            {
              loading('play', false);
              addResults(res);
              _EDITOR.focus();
            }, 1000); */
}

// change language highlighting of editor
function changeMode(mode)
{
	_EDITOR.getSession().setMode('ace/mode/' + mode.replace(' ', '_'));  
}

// change font Size of editor
function changeFontSize(pt)
{
    var e = document.getElementById("editor");
    e.style.fontSize = pt + "pt";
    
    _FONTSIZE = pt;
    setCookie('_FONTSIZE', Math.floor(pt*2)/2, _COOKIE_EX_DAYS);
}

// change font size of content
function changeFontSize(percent)
{
    var e = document.getElementById("editor");
    e.style.fontSize = (percent/2) + "%";
    e.nextElementSibling.style.fontSize = Math.min(150, percent) + '%';
    
    _FONTSIZE = percent;
    setCookie('_FONTSIZE', Math.floor(percent*2)/2, _COOKIE_EX_DAYS);
}


var Range = require('ace/range').Range;
// set editor preferences
function initEditor()
{
    _EDITOR = ace.edit("editor");
    _EDITOR.renderer.setHScrollBarAlwaysVisible(false);
    _EDITOR.setTheme("ace/theme/eclipse");
	_EDITOR.getSession().setMode('ace/mode/c_cpp'); //equv to: changeMode('c_cpp');
    _EDITOR.renderer.setShowGutter(true);
    _EDITOR.setShowPrintMargin(true);
    _EDITOR.setDisplayIndentGuides(true);
    _EDITOR.setHighlightSelectedWord(true);
    _EDITOR.setPrintMarginColumn(80);
    
    _EDITOR.session.setValue(_INIT_CODE);
    _EDITOR.session.setTabSize(4);
    _EDITOR.session.setUseWrapMode(true);

    _EDITOR.session.on("change", clearResults);
    $('.ace_text-input').bind('keyup',   clearSampleAndResults); 
    $('.ace_text-input').bind('mouseup', clearSampleAndResults); 

    _EDITOR.on("gutterclick", highlightCodeByAnnotation);

    _EDITOR.commands.addCommand({
        name: 'execute',
        bindKey: {win: 'Ctrl-D',  mac: 'Command-D'},
        exec: getResults,
        readOnly: true
    });

    _EDITOR.commands.addCommand({
        name: 'execute',
        bindKey: {win: 'Ctrl-S',  mac: 'Command-S'},
        exec: function() { getResults(); toast('Save file not possible!'); },
        readOnly: true
    });
}


