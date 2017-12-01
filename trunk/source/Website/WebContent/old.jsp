<%@ page language="java" contentType="text/html; charset=UTF-8" pageEncoding="UTF-8"%>
<%--
Params:
- task={VerifyBoogie, VerifyC, RunAutomataTestFile, RunSmt2Script}
- fontSize=true
--%>
<%@ taglib prefix="c" uri="http://java.sun.com/jsp/jstl/core"%>
<%@ page trimDirectiveWhitespaces="true"%>
<%@ page import="java.util.*"%>
<%@ page import="de.uni_freiburg.informatik.ultimate.webbridge.website.WebToolchain" %>
<%@ page import="de.uni_freiburg.informatik.ultimate.webbridge.website.Tasks" %>
<%@ page import="de.uni_freiburg.informatik.ultimate.webbridge.website.Example" %>
<%@ page import="de.uni_freiburg.informatik.ultimate.webbridge.website.Tool" %>
<%@ page import="de.uni_freiburg.informatik.ultimate.webbridge.website.Setting" %>
<%@ page import="de.uni_freiburg.informatik.ultimate.webbridge.toolchains.*" %>
<%@ page import="java.text.DateFormat" %>
<%@ page import="java.text.SimpleDateFormat" %>
<%
    Tasks tasks = new Tasks();
    Map<String, ArrayList<WebToolchain>> toolchains = Tasks.getActiveToolchains();
    Map<Tasks.TaskNames, ArrayList<Example>> examples = Example.getExamples();
    pageContext.setAttribute("tasks", tasks);
    pageContext.setAttribute("examples", examples);
    pageContext.setAttribute("toolchains", toolchains);
%>
<!DOCTYPE html>
<html xmlns="http://www.w3.org/1999/xhtml">
<head>
    <meta http-equiv="Content-Type" content="text/html; charset=UTF-8"/>
    <meta name="author" content="Markus Lindenmann, Oleksii Saukh, Stefan Wissert" />
    <meta name="viewport" content="initial-scale=1.0, user-scalable=no" />
    <link rel="shortcut icon" type="image/x-icon" href="./favicon.ico">
    <link rel="stylesheet" type="text/css" media="screen, projection" href="./css-old/main.css">
    <!--[if lt IE 9]><script src="//html5shiv.googlecode.com/svn/trunk/html5.js"></script><![endif]-->
    <script type="text/javascript" charset="utf-8" src="./js-old/ace/ace.js"></script>
    <script type="text/javascript" charset="utf-8" src="./js-old/ace/themes/theme-eclipse.js"></script>
    <script type="text/javascript" charset="utf-8" src="./js-old/ace/modes/mode-c.js"></script>
    <script type="text/javascript" charset="utf-8" src="./js-old/ace/modes/mode-boogie.js"></script>
    <script type="text/javascript" charset="utf-8" src="./js-old/jquery-1.7.2.min.js"></script>
    <script type="text/javascript" charset="utf-8" src="./js-old/main.jsp"></script>
    <title>Uni-Freiburg : SWT - Ultimate</title>
</head>
<body>
    <div id="wrapper">
        <header id="header">
            <h1>Ultimate Web-Interface</h1>
        </header>
        <section id="middle">
            <div id="sideLeft">
                <div class="sub_menu">
                    <form id="SetEditor">
                        <p>
                        <label class="main_opt" for="sel_mode">Task:</label>
                        <select name="sel_mode" size="1" onchange="changeTask()">
                            <c:if test="${param.task eq null || param.task eq ''}">
                            <option selected="selected" value="">_ Select a Task _</option>
                            </c:if>
                            <c:forEach items="${tasks.getTaskString()}" var="t">
                            <c:choose><c:when test="${param.task eq null || param.task eq ''}">
                            <option value="<c:out value="${t.key},${tasks.getSyntaxHighlightingMode(t.key)}" />"><c:out value="${t.value}" /></option>
                            </c:when><c:otherwise>
                            <option <c:if test="${t.key.toString() eq param.task}">selected="selected" </c:if>value="<c:out value="${t.key},${tasks.getSyntaxHighlightingMode(t.key)}" />"><c:out value="${t.value}" /></option>
                            </c:otherwise>
                            </c:choose>
                            </c:forEach>
                        </select>
                        </p>
                    </form>
                </div>
                <div class="sub_menu">
                    <c:forEach items="${examples}" var="list">
                    <form id="SetExamples${list.key}">
                        <p>
                        <label class="main_opt" for="sel_examples">Sample:</label>
                        <select class="sel_examples" name="sel_examples" size="1" onchange="selectExample()">
<c:if test="${param.example eq null || param.example eq ''}">
 <option selected="selected" value="">_ Select Example _</option>
 </c:if>
 <c:forEach items="${list.value}" var="example">
 <c:choose><c:when test="${param.example eq null || param.example eq ''}">
 <option value="<c:out value="${example.getId()}" />"><c:out value="${example.getFileName()}" /></option>
 </c:when><c:otherwise>
 <option <c:if test="${example.getId() eq param.example}">selected="selected" </c:if>value="<c:out value="${example.getId()}" />"><c:out value="${example.getFileName()}" /></option>
 </c:otherwise>
 </c:choose>
                            </c:forEach>
                        </select>
                        </p>
                    </form>
                    </c:forEach>
                </div>
                <div class="sub_menu">
                    <c:forEach items="${toolchains}" var="tcs">
                    <form id="SetTC${tcs.key}">
                        <p>
                        <label class="main_opt" for="sel_toolchain${tcs.key}">Tool:</label>
                        <select name="sel_toolchain" size="1" onchange="selectToolchain${tcs.key}()">
                            <c:forEach items="${tcs.value}" var="listItem">
                            <option value="<c:out value="${listItem.getId()}" />"><c:out value="${listItem.getName()}" /></option>
                            </c:forEach>
                        </select>
                        </p>
                    </form>
                    </c:forEach>
                    <c:forEach items="${toolchains}" var="tcs">
                    <div id="taskInfo${tcs.key}">
                        <c:forEach items="${tcs.value}" var="tc">
                        <div id="metaInfo${tc.getId()}">
                        <p id="desc${tcs.key}${tc.getId()}" class="description"><c:out value="${tc.getDescription()}" /></p>
                        <a class="cp_toggle_tc_settings" id="cp_toggle_tc_settings${tc.getId()}" href="#">Settings</a>
                        <div class="cp_div_tc_settings" id="cp_div_tc_settings${tc.getId()}">
                        <form id="SetTC${tc.getId()}">
                            <input type="hidden" name="taskID" value="${tcs.key}" />
                            <input type="hidden" name="tcID" value="${tc.getId()}" />
                            <div id="settings${tc.getId()}">
                            <c:forEach items="${tc.getTools()}" var="tool">
                                <c:forEach items="${tool.getUserChangeableSettings()}" var="setting">
                                <p class="indent" id="SetTCSettings${tc.getId()}${tool.getHTMLId()}">
                                    <label class="main_opt"><c:out value="${setting.getSettingDescription()}"/>
                                    <c:choose>
                                        <c:when test="${setting.getType() eq 'DROPDOWN'}">
                                        <select name="sel_tc_${tc.getId()}_${tool.getHTMLId()}_${setting.getSettingIdentifier()}" <c:choose><c:when test="${setting.isMultiSelectable()}">multimple="multiple"</c:when><c:otherwise>size="1"</c:otherwise></c:choose> onchange="selectToolchain${tcs.key}()">
                                            <c:forEach items="${setting.getValues()}" var="option">
                                            <option value="<c:out value="${option}" />"><c:out value="${option}" /></option>
                                            </c:forEach>
                                        </select>
                                        </c:when><c:when test="${setting.getType() eq 'STRING'}">
                                        <input type="text" name="sel_tc_${tc.getId()}_${tool.getHTMLId()}_${setting.getSettingIdentifier()}" value='<c:out value="${setting.getDefaultValue()[0]}"></c:out>' />
                                        </c:when><c:when test="${setting.getType() eq 'BOOLEAN'}">
                                        <input type="checkbox" name="sel_tc_${tc.getId()}_${tool.getHTMLId()}_${setting.getSettingIdentifier()}" value="${setting.getSettingIdentifier()}" <c:if test="${setting.getDefaultValue()[0] eq 'true'}">checked</c:if> /><br />
                                        </c:when><c:when test="${setting.getType() eq 'INTEGER'}">
                                        <input type="number" name="sel_tc_${tc.getId()}_${tool.getHTMLId()}_${setting.getSettingIdentifier()}" value='<c:out value="${setting.getDefaultValue()[0]}"></c:out>' />
                                        </c:when><c:otherwise>
                                        <%System.out.println(new SimpleDateFormat("dd.MM.yyyy HH:mm:ss").format(new Date()) + " Unknown setting type");%>
                                        </c:otherwise>
                                    </c:choose>
                                    </label>
                                </p>
                                </c:forEach>
                            </c:forEach>
                            </div>
                        </form>
                        </div> <%-- / cp_div_tc_settings${tc.getId()} --%>
                        </div> <%-- / metaInfo --%>
                        </c:forEach>
                    </div> <%-- / taskInfo --%>
                    </c:forEach>
                </div> <%-- / sub menu --%>
                <div id="editorOptions">
                    <form id="SetEditor">
                    <a id="evaluate" href="#">Execute</a><br />
                    <c:if test="${param.fontSize eq 'true'}">
                    <div>
                  <label class="main_opt" for="sel_font_size">Font size:</label>
                  <select id="SelFontSize" name="sel_font_size" size="1" onchange="changeFontSize()">
                  <c:forEach var="num" begin="8" end="20" step="2">
                      <option <c:if test="${num == 10}">selected="selected" </c:if>value="<c:out value="${num}"/>"><c:out value="${num}"/></option>
                  </c:forEach>
                  </select>
                  </div>
                  </c:if>
                  <br />
                  <a id="editor_toggle" href="#"></a>
                  <input type="file" id="openFile" name="files[]" <%-- multiple --%>/>
                </form>
              </div>
            </div> <%-- / side left --%>
            <div id="container">
                <div id="content">
                    <div id="editor"></div>
                    <div id="server_messages">
                        <div id="srv_msg"></div>
                    </div>
                </div>
            </div>
            <div class="clear"></div>
        </section>
    </div>
</body>
</html>
