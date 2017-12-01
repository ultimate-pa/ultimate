<%@ page language="java" contentType="application/javascript; charset=UTF-8" pageEncoding="UTF-8"%>
<%@ taglib prefix="c" uri="http://java.sun.com/jsp/jstl/core" %>
<%@ page trimDirectiveWhitespaces="true" %>
<%@ page import="java.util.*" %>
<%@ page import="de.uni_freiburg.informatik.ultimate.webbridge.website.WebToolchain" %>
<%@ page import="de.uni_freiburg.informatik.ultimate.webbridge.website.Tasks" %>
<%@ page import="de.uni_freiburg.informatik.ultimate.webbridge.website.Example" %>
<%@ page import="de.uni_freiburg.informatik.ultimate.webbridge.toolchains.*" %>
<%
    Tasks tasks = new Tasks();
    Map<String, ArrayList<WebToolchain>> toolchains = Tasks.getActiveToolchains();
    Map<Tasks.TaskNames, ArrayList<Example>> examples = Example.getExamples();
    pageContext.setAttribute("examples", examples);
    pageContext.setAttribute("toolchains", toolchains);
%>
<%-- @author Markus Lindenmann, Oleksii Saukh, Stefan Wissert
    @since 10.10.2011
    
    VALIDATED WITH: http://www.jslint.com/ --%>
<%-- The address, where we can find the server. --%>
var server = "../WebsiteEclipseBridge/if?callback=?";
<%-- The ACE editor instance. --%>
var editor;
<%-- The initial text of the ACE editor. --%>
var INIT_CODE = "// Enter Code here ...";
<%-- A helper variable for the editor toggle function. --%>
var toggleEditorHeight = true;
<%-- Hides all menus. --%>
function hideAll() {
    "use strict";
    <c:forEach items="${toolchains}" var="tcs"><c:forEach items="${tcs.value}" var="tc">
    $('#cp_div_tc_settings${tc.getId()}').hide();
    </c:forEach></c:forEach>
}
<%-- Toggles the editor between 100% height and 50% height. --%>
function toggleEditor() {
    "use strict";
    var e = document.getElementById("editor");
    if (toggleEditorHeight) {
        $('#server_messages').show();
        e.style.height = '70%';
        document.getElementById('server_messages').style.height = '30%';
        $('#editor_toggle').html("Show editor fullscreen");
    } else {
        $('#server_messages').hide();
        e.style.height = '100%';
        document.getElementById('server_messages').style.height = '0%';
        $('#editor_toggle').html("Show Ultimate results");
    }
    editor.resize();
    toggleEditorHeight = !toggleEditorHeight;
}
<%-- encode arbitrary string to html string --%>
<%-- additionally all linebreaks are replaced by <br /> and all tabulators are replaced by 4 html spaces --%>
function htmlEncode(value){
  return $('<div />').text(value).html().replace(/(\r\n|\n|\r)/gm,"<br />").replace(/\t/g,"&nbsp;&nbsp;&nbsp;&nbsp;");
}
<%--decode html string to decoded string --%>
function htmlDecode(value){
  return $('<div />').html(value).text();
}
<%-- Evaluate the entered code. --%>
function getResult() {
    "use strict";
    var trimmedCode = $.trim(editor.getSession().getValue());
    if (trimmedCode !== "" && trimmedCode !== INIT_CODE) {
        if (toggleEditorHeight) {
            toggleEditor();
            $('#editor_toggle').show();
        }
        <%-- Get corresponding settings from the form --%>
        var obj = document.getElementById("SetEditor");
        var idx = obj.sel_mode.selectedIndex;
        var task = obj.sel_mode.options[idx].value.split(",")[0];
        if (task == "") {
            alert("Please select a task!");
            return;
        }
        var obj = document.getElementById("SetTC"+task);
        var idx = obj.sel_toolchain.selectedIndex;
        var tcId = obj.sel_toolchain.options[idx].value;
        var settings = $("#SetTC"+tcId).serialize();
        $('#srv_msg').html("<pre><img src=\"./img-old/wait.gif\"/>&nbsp;Ultimate started, please wait ...</pre>");
        <%-- Compose the Post message --%>
        var values = "action=execute";
        values += "&code=" + encodeURIComponent(trimmedCode);
        values += "&" + settings;
        $.post(server, values, function (json) {
            if (json.error != null) {
                alert("Error:\n\n"+json.error);
                return;
            } else if(json.status == "success") {
                var annot = new Array();
                if (!json.results) {
                    $('#srv_msg').html("<pre>No results</pre>");
                    return;
                }
                var table = "<table id=\"resultTable\" border=1>";
                table += "<col width=\"25px\" /><col width=\"50px\" /><col width=\"*\" />";
                table += "<tr><th>&nbsp;</th><th>Line</th><th>Ultimate Result</th></tr>";
                $.each(json.results, function(idx) {
                    var result = json.results[idx];
                <%-- Annotations --%>
                annot[idx] = {
                        row: result.startLNr - 1,
                        text: result.shortDesc,
                        type: result.logLvl
                    };
                <%-- Marker --%>
                <%--Table --%>
                table += "<tr><td class=\"" + htmlEncode(result.logLvl) + "\">&nbsp;</td>";
                table += "<td>" + htmlEncode(result.startLNr);
                if (result.endLNr != 0 && result.startLNr != result.endLNr) {
                  table += " - " + htmlEncode(result.endLNr)
                }
                table += "</td><td class=\"left\">";
                table += "<b>" + htmlEncode(result.shortDesc) + "</b><br />";
                table += htmlEncode(result.longDesc);
                table += "</td></tr>";
            });
            editor.getSession().setAnnotations(annot);
                $('#srv_msg').html(table);
            } else {
                alert("Unexpected response from server!");
            }
        }, "json");
    } else {
        alert("Nothing to do ;)\n\nPlease enter some code before you try to evaluate!");
    }
}
<%-- Load a file into the editor.
    @param evt the event to handle --%>
function handleFileSelect(evt) {
    "use strict";
    var files = evt.target.files;
    
    for (var i = 0, file; file = files[i]; i++) {
        if (!(file.type.match('text.*') || file.type == '')
                || file.size >= 20000) {
            if (file.size >= 20000) {
                alert("File to large!\nSkipped: "+file.name);
            } else {
                alert("Cannot open files of type: " + file.type + "\nSkipped: "+file.name);
            }
            continue;
        }
        var reader = new FileReader();
        reader.onload = (function(theFile) {
            return function(e) {
                <%-- var before = editor.getSession().getValue(); --%>
                <%-- window.open('Interface.jsp?','_newtab'); --%>
                editor.getSession().setValue(<%--before + "\n" + 
                        "// " + escape(theFile.name) + "\n" +--%> e.target.result <%--+ "\n"--%>);
            };
        })(file);
        reader.readAsText(file);
    }
}
<%-- Control panel menu functionality. --%>
function controlPanel() {
    "use strict";
    $('#openFile').bind('change', false, handleFileSelect);
    $("a#evaluate").click(function () {
        getResult();
    });
    hideAll();
    $("a#cp_toggle_editor").click(function () {
        $('#cp_div_editor').fadeToggle();
    });
    <c:forEach items="${toolchains}" var="tcs"><c:forEach items="${tcs.value}" var="tc">
    $("a#cp_toggle_tc_settings${tc.getId()}").click(function () {
        $('#cp_div_tc_settings${tc.getId()}').fadeToggle();
    });
    </c:forEach></c:forEach>
    $("a#editor_toggle").click(function () {
        toggleEditor();
    });
}
<%-- Change editors syntax mode. --%>
function changeMode(mode) {
    "use strict";
    var SetToMode = require("ace/mode/" + mode).Mode;
    editor.getSession().setMode(new SetToMode());
}
<%-- Initialize the editor element. --%>
function initEditor() {
    "use strict";
    editor = ace.edit("editor");
    editor.renderer.setHScrollBarAlwaysVisible(false);
    editor.setTheme("ace/theme/eclipse");
    changeMode("c_cpp");
    editor.renderer.setShowGutter(true);
    editor.getSession().setValue(INIT_CODE);
    editor.getSession().setTabSize(4);
    editor.getSession().setUseWrapMode(true);
    
    $('#editor_toggle').hide();
    editor.getSession().on('change', function() {
        editor.getSession().setAnnotations([]);
    });
}
<%-- Change editors font size. --%>
function changeFontSize() {
    "use strict";
    var obj = document.getElementById("SelFontSize");
    var e = document.getElementById("editor");
    var idx = obj.selectedIndex;
    e.style.fontSize = obj.options[idx].value + "pt";
}
 <c:forEach items="${toolchains}" var="tcs">
<%-- Onchange method for the <c:out value="${tcs.key}" /> select toolchain form. --%>
function selectToolchain<c:out value="${tcs.key}" />() {
    "use strict";
    var obj = document.getElementById("SetTC${tcs.key}");
    var idx = obj.sel_toolchain.selectedIndex;
    var tcId = obj.sel_toolchain.options[idx].value;
    <%-- show only applicable description and settings --%>
    <c:forEach items="${tcs.value}" var="tc">
    if("${tc.getId()}" != tcId) {
        $('#metaInfo${tc.getId()}').hide();
    } else {
        $('#metaInfo${tc.getId()}').show();
    }
    </c:forEach>
}
</c:forEach>
<%-- Onchange method for the task select form. --%>
function changeTask() {
    "use strict";
    var obj = document.getElementById("SetEditor");
    var idx = obj.sel_mode.selectedIndex;
    var mode = obj.sel_mode.options[idx].value;
    <%-- Reset all example dropdowns to 0 --%>
    $('.sel_examples').each(function(i){this.selectedIndex = 0;});
    if (mode == "") {
        <c:forEach items="${toolchains}" var="tcs">
        $('#SetTC${tcs.key}').hide();
        $('#taskInfo${tcs.key}').hide();
        </c:forEach>
        <c:forEach items="${examples}" var="list">$('#SetExamples${list.key}').hide();</c:forEach>
        return;
    }
    var res = mode.split(",");
    changeMode(res[1]);
    <%-- show only applicable toolcahins and settings --%>
    <c:forEach items="${toolchains}" var="tcs">
    if ("${tcs.key.toString()}" != res[0]) {
        $('#SetTC${tcs.key}').hide();
        $('#taskInfo${tcs.key}').hide();
    } else {
        $('#SetTC${tcs.key}').show();
        $('#taskInfo${tcs.key}').show();
    }
    </c:forEach>
    <%-- show only applicable examples --%>
    <c:forEach items="${examples}" var="list">
    if ("${list.key.toString()}" != res[0]) {
        $('#SetExamples${list.key}').hide();
    } else {
        $('#SetExamples${list.key}').show();
    }
    </c:forEach>
}
<%-- Onchange method for the example select form. --%>
function selectExample() {
    "use strict";
    editor.getSession().setAnnotations([]);
    var obj = document.getElementById("SetEditor");
    var idx = obj.sel_mode.selectedIndex;
    var mode = obj.sel_mode.options[idx].value;
    if (mode == "") {
      return;
    }
    var task = mode.split(",")[0];
    obj = document.getElementById("SetExamples"+task);
    idx = obj.sel_examples.selectedIndex;
    var selExample = obj.sel_examples.options[idx].value;
    if (selExample == "") {
      return;
    }
    $.get(server, "example=" + encodeURIComponent(selExample), function (json) {
        if (json.exampleContent !== null) {
            editor.getSession().setValue(json.exampleContent);
            return;
        }
    }, "json");
}
<%-- The entry point. --%>
$(document).ready(function () {
    "use strict";
    initEditor();
    <c:forEach items="${toolchains}" var="tcs">selectToolchain<c:out value="${tcs.key}" />();</c:forEach>
    selectExample();
    changeTask();
    controlPanel();
    $('#server_messages').hide();
});