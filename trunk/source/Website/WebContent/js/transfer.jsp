<%@ page language="java" contentType="application/javascript; charset=UTF-8" pageEncoding="UTF-8"%>
<%@ page import="de.uni_freiburg.informatik.ultimate.webbridge.website.WebToolchain"%>
<%@ page import="de.uni_freiburg.informatik.ultimate.webbridge.website.Tasks"%>
<%@ page import="de.uni_freiburg.informatik.ultimate.webbridge.website.Worker"%>
<%@ page import="de.uni_freiburg.informatik.ultimate.webbridge.website.Example"%>
<%@ page import="org.json.simple.JSONObject"%>
<%@ page import="java.util.*"%>
<%@ taglib prefix="c" uri="http://java.sun.com/jsp/jstl/core"%>
<%
	int s = PageContext.SESSION_SCOPE;
 
  @SuppressWarnings("unchecked")
	Map<Tasks.TaskNames, ArrayList<Example>> examples = (Map<Tasks.TaskNames, ArrayList<Example>>) pageContext.getAttribute("examples", s);
  @SuppressWarnings("unchecked")
  Map<String, Worker> currentWorker = (Map<String, Worker>) pageContext.getAttribute("currentWorker", s);
  @SuppressWarnings("unchecked")
  
  Map<String, Worker> worker = (Map<String, Worker>) pageContext.getAttribute("worker", s);
  JSONObject content = (JSONObject) pageContext.getAttribute("content", s);
%>

var _SERVER_INFO =
            [
              <% // de.uni_freiburg.informatik.ultimate.webbridge.toolchains:*TC.java::setUserInfo()%>
              <c:forEach items="${worker[param.tool].getToolchains()}" var="tc">"<c:out value="${tc.getUserInfo()}" default="" escapeXml="false" />",</c:forEach>
              <% // de.uni_freiburg.informatik.ultimate.webbridge.website:Tasks.java::initWorkers()%>
              "<c:out value="${worker[param.tool].getUserInfo()}" default="" />",
              <% // /Website/<tool>.json%>
              "<c:out value="${content.user_info}" default="" />"
            ];

var _ITEMS =
                {
                  <c:forEach items="${currentWorker}" var="w">
                    "<c:out value="${w.key}" default="" />":
                    {
                      "id": "<c:out value="${w.value.getId()}" default="" />",
                      "name": "<c:out value="${w.value.getName()}" default="" />",
                      "spinnerID": "tool",
                      "children":
                      [
                        <c:forEach items="${w.value.getToolchains()}" var="tc">
                          "<c:out value="${tc.getId()}" default="" />",
                        </c:forEach>
                      ],
                      "preferences":
                      {
                         <c:if test="${w.value.getInterfaceLayoutFontsize() ne null}">
                           "fontsize": "<c:out value="${w.value.getInterfaceLayoutFontsize()}" default="" />",
                         </c:if>
                         <c:if test="${w.value.getInterfaceLayoutOrientation() ne null}">
                           "orientation": "<c:out value="${w.value.getInterfaceLayoutOrientation()}" default="" />",
                         </c:if>
                         <c:if test="${w.value.getInterfaceLayoutTransitions() ne null}">
                           "transitions": "<c:out value="${w.value.getInterfaceLayoutTransitions()}" default="" />",
                         </c:if>
                      },
                      "parentID": null,
                      "evalText": "<c:out value="${w.value.getLabel()}" default="" />"
                    },
                  </c:forEach>
                  <c:forEach items="${currentWorker}" var="w">
	                  <c:forEach items="${w.value.getToolchains()}" var="tc">
	                    "<c:out value="${tc.getId()}" default="" />":
	                      {
                          "id": "<c:out value="${tc.getId()}" default="" />",
                          "taskID": "<c:out value="${tc.getTaskName()[0]}" default="" />",
	                        "name": "<c:out value="${tc.getLanguage()}" default="" />",
	                        "language": "<c:out value="${tc.getLanguage()}" default="" />",
	                        "spinnerID": "task",
	                        "parentID": "<c:out value="${w.value.getId()}" default="" />",
	                        "children":
	                        [
	                          <c:forEach items="${tc.getTaskName()}" var="tn">
	                            <c:forEach items="${examples}" var="list">
	                              <c:if test="${list.key eq tn}">
	                                <c:forEach items="${list.value}" var="example">
	                                  "<c:out value="${example.getId()}" default="" />",
	                                </c:forEach>
	                              </c:if>
	                            </c:forEach>
	                          </c:forEach>
	                        ],
                          "settings":
                          [
                              <c:forEach items="${tc.getUserModifiableSettings()}" var="setting">
                                "<c:out value="${tc.getId()}" default="" />_<c:out value="${setting.getSettingIdentifier()}" default="" />",
                              </c:forEach>
                          ],
                          "preferences":
                          {
                             <c:if test="${tc.getInterfaceLayoutFontsize() ne null}">
                               "fontsize": "<c:out value="${tc.getInterfaceLayoutFontsize()}" default="" />",
                             </c:if>
                             <c:if test="${tc.getInterfaceLayoutOrientation() ne null}">
                               "orientation": "<c:out value="${tc.getInterfaceLayoutOrientation()}" default="" />",
                             </c:if>
                             <c:if test="${tc.getInterfaceLayoutTransitions() ne null}">
                               "transitions": "<c:out value="${tc.getInterfaceLayoutTransitions()}" default="" />",
                             </c:if>
                          }
	                      },
	                  </c:forEach>
                  </c:forEach>
                  
                  <c:forEach items="${examples}" var="list">
                    <c:forEach items="${list.value}" var="example">
                        "<c:out value="${example.getId()}" default="" />":
                        {
                          "id": "<c:out value="${example.getId()}" default="" />",
                          "name": "<c:out value="${example.getFileName()}" default="" />",
                          "spinnerID": "samples"
                        },
                    </c:forEach>
                  </c:forEach>

                  <c:forEach items="${currentWorker}" var="w">
	                  <c:forEach items="${w.value.getToolchains()}" var="tc">
	                      <c:forEach items="${tc.getUserModifiableSettings()}" var="setting">
		                      <c:forEach items="${setting.getValues()}" var="item">
		                        "<c:out value="${item}" default="" />":
		                        {
		                          "id": "<c:out value="${item}" default="" />",
		                          "name": "<c:out value="${item}" default="" />",
		                          "spinnerID": "<c:out value="${setting.getSettingIdentifier()}" default="" />"
	                          },  
		                      </c:forEach>
	                      </c:forEach>
	                    </c:forEach>
                  </c:forEach>

                };
var _SETTINGS = {
                  <c:forEach items="${currentWorker}" var="w">
                    <c:forEach items="${w.value.getToolchains()}" var="tc">
		                    <c:forEach items="${tc.getUserModifiableSettings()}" var="setting">
		                      "<c:out value="${tc.getId()}" default="" />_<c:out value="${setting.getSettingIdentifier()}" default="" />":
		                      {
	                           "id": "<c:out value="${setting.getSettingIdentifier()}" default="" />",
	                           "type": "<c:out value="${setting.getType()}" default="" />",
	                           "label": "<c:out value="${setting.getSettingDescription()}" default="" />",
	                           "value": "<c:out value="${setting.getDefaultValue()[0]}" default="" />",
                               "prefix": "<c:out value="${tc.getId()}" default="" />_",
	                           "items":
		                           [
		                              <c:forEach items="${setting.getValues()}" var="item">
	  	                              "<c:out value="${item}" default="" />",
		                              </c:forEach>
		                           ],
	                           "multi": "<c:out value="${setting.isMultiSelectable()}" default="" />"
		                      },
		                    </c:forEach>
                    </c:forEach>
                  </c:forEach>
                };