<%@ taglib prefix="c" uri="http://java.sun.com/jsp/jstl/core"%>
<%@ page language="java" contentType="application/javascript; charset=UTF-8" pageEncoding="UTF-8"%>


var _SERVER_INFO =
            [
              <!-- de.uni_freiburg.informatik.ultimate.website.toolchains:*TC.java::setUserInfo() -->
              <c:forEach items="${worker[param.tool].getToolchains()}" var="tc">"<c:out value="${tc.getUserInfo()}" default="" escapeXml="false" />",</c:forEach>
              <!-- de.uni_freiburg.informatik.ultimate.website:Tasks.java::initWorkers() -->
              "<c:out value="${worker[param.tool].getUserInfo()}" default="" />",
              <!-- /Website/tool.json -->
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
	                          <c:forEach items="${tc.getTools()}" var="tool">
	                            <c:forEach items="${tool.getUserChangeableSettings()}" var="setting">
	                              "<c:out value="${setting.getSettingIdentifier()}" default="" />",
	                            </c:forEach>
	                          </c:forEach>
	                        ]
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
	                    <c:forEach items="${tc.getTools()}" var="tool">
	                      <c:forEach items="${tool.getUserChangeableSettings()}" var="setting">
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
                  </c:forEach>

                };
var _SETTINGS = {
                  <c:forEach items="${currentWorker}" var="w">
                    <c:forEach items="${w.value.getToolchains()}" var="tc">
		                  <c:forEach items="${tc.getTools()}" var="tool">
		                    <c:forEach items="${tool.getUserChangeableSettings()}" var="setting">
		                      "<c:out value="${setting.getSettingIdentifier()}" default="" />":
		                      {
	                           "id": "<c:out value="${setting.getSettingIdentifier()}" default="" />",
	                           "type": "<c:out value="${setting.getType()}" default="" />",
	                           "label": "<c:out value="${setting.getSettingDescription()}" default="" />",
	                           "value": "<c:out value="${setting.getDefaultValue()[0]}" default="" />",
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
                  </c:forEach>
                };