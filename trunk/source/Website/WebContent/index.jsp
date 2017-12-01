<%--
Params:
- ui={<empty>, home, tool, int}
- tool={LassoRanker, BuchiAutomizer, TraceAbstraction, AutomataScript, ConcurrentTraceAbstraction}
- task={VerifyBoogie, VerifyC, RunAutomataTestFile, RunSmt2Script}
- sample={}
--%>
<%@ page import="java.nio.charset.StandardCharsets"%>
<%@ page import="org.apache.catalina.core.ApplicationContext"%>
<%@ taglib prefix="c" uri="http://java.sun.com/jsp/jstl/core"%>
<%@ page trimDirectiveWhitespaces="true"%>
<%@ page import="java.util.*"%>
<%@ page
	import="de.uni_freiburg.informatik.ultimate.webbridge.website.WebToolchain"%>
<%@ page
	import="de.uni_freiburg.informatik.ultimate.webbridge.website.Tasks"%>
<%@ page
	import="de.uni_freiburg.informatik.ultimate.webbridge.website.Worker"%>
<%@ page
	import="de.uni_freiburg.informatik.ultimate.webbridge.website.Example"%>
<%@ page
	import="de.uni_freiburg.informatik.ultimate.webbridge.website.Tool"%>
<%@ page
	import="de.uni_freiburg.informatik.ultimate.webbridge.website.Setting"%>
<%@ page
	import="de.uni_freiburg.informatik.ultimate.webbridge.toolchains.*"%>
<%@ page import="java.text.DateFormat"%>
<%@ page import="java.text.SimpleDateFormat"%>
<%@ page import="java.io.BufferedReader"%>
<%@ page import="java.io.InputStream"%>
<%@ page import="java.io.InputStreamReader"%>
<%@ page import="java.io.IOException"%>
<%@ page import="java.io.FileNotFoundException"%>
<%@ page import="java.net.HttpURLConnection"%>
<%@ page import="java.net.URLConnection"%>
<%@ page import="java.net.URLEncoder"%>
<%@ page import="java.net.URLDecoder"%>
<%@ page import="java.net.URL"%>
<%@ page import="java.io.File"%>
<%@ page import="java.io.FileInputStream"%>

<%@ page import="org.json.simple.JSONObject"%>
<%@ page import="org.json.simple.JSONValue"%>
<%@ page import="org.json.simple.JSONArray"%>

<%!String getData(String address) throws Exception {
		System.out.println("Requesting URL " + address);
		URL page = new URL(address);
		StringBuffer text = new StringBuffer();
		HttpURLConnection conn = (HttpURLConnection) page.openConnection();
		BufferedReader buff = new BufferedReader(
				new InputStreamReader(openConnectionCheckRedirects(conn), StandardCharsets.UTF_8));

		String line = new String();
		while (true) {
			line = buff.readLine();
			if (line == null)
				break;
			text.append(line + "\n");
		}
		buff.close();
		return text.toString();
	}

	private InputStream openConnectionCheckRedirects(URLConnection c) throws IOException {
		boolean redir;
		int redirects = 0;
		InputStream in = null;
		do {
			if (c instanceof HttpURLConnection) {
				((HttpURLConnection) c).setInstanceFollowRedirects(false);
			}
			// We want to open the input stream before getting headers
			// because getHeaderField() et al swallow IOExceptions.
			in = c.getInputStream();
			redir = false;
			if (c instanceof HttpURLConnection) {
				HttpURLConnection http = (HttpURLConnection) c;
				int stat = http.getResponseCode();
				if (stat >= 300 && stat <= 307 && stat != 306 && stat != HttpURLConnection.HTTP_NOT_MODIFIED) {
					// we follow redirects in certain cases. For convenience, here is the Wikipedia cutnpaste
					/*
					300 Multiple Choices
					Indicates multiple options for the resource that the client may follow. 
					It, for instance, could be used to present different format options for video, 
					list files with different extensions, or word sense disambiguation.
					
					301 Moved Permanently
					This and all future requests should be directed to the given URI.
					
					302 Found
					This is an example of industry practice contradicting the standard. 
					The HTTP/1.0 specification (RFC 1945) required the client to perform a 
					temporary redirect (the original describing phrase was "Moved Temporarily"),
					[6] but popular browsers implemented 302 with the functionality of a 303 See Other. 
					Therefore, HTTP/1.1 added status codes 303 and 307 to distinguish between the 
					two behaviours.[7] However, some Web applications and frameworks use the 302 
					status code as if it were the 303.[8]
					
					303 See Other (since HTTP/1.1)
					The response to the request can be found under another URI using a GET method. 
					When received in response to a POST (or PUT/DELETE), it should be assumed that 
					the server has received the data and the redirect should be issued with a separate 
					GET message.
					
					304 Not Modified
					Indicates that the resource has not been modified since the version specified 
					by the request headers If-Modified-Since or If-None-Match. This means that there 
					is no need to retransmit the resource, since the client still has a 
					previously-downloaded copy.
					
					305 Use Proxy (since HTTP/1.1)
					The requested resource is only available through a proxy, 
					whose address is provided in the response. Many HTTP clients 
					(such as Mozilla[9] and Internet Explorer) do not correctly handle responses with 
					this status code, primarily for security reasons.[10]
					
					306 Switch Proxy
					No longer used. 
					Originally meant "Subsequent requests should use the specified proxy."[11]
					
					307 Temporary Redirect (since HTTP/1.1)
					In this case, the request should be repeated with another URI; 
					however, future requests should still use the original URI. 
					In contrast to how 302 was historically implemented, the request method is not 
					allowed to be changed when reissuing the original request. For instance, a POST 
					request should be repeated using another POST request.[12]
					 */

					URL base = http.getURL();
					String loc = http.getHeaderField("Location");
					URL target = null;
					if (loc != null) {
						target = new URL(base, loc);
					}
					http.disconnect();
					// Redirection should be allowed only for HTTP and HTTPS
					// and should be limited to 5 redirections at most.
					if (target == null || !(target.getProtocol().equals("http") || target.getProtocol().equals("https"))
							|| redirects >= 5) {
						String errorMsg = "";
						if (target == null) {
							errorMsg = "Target is null";
						} else if (redirects >= 5) {
							errorMsg = "There are more than 5 redirects";
						} else {
							errorMsg = "The redirect points to an illegal protocol: " + target.getProtocol();
						}
						throw new IOException("Illegal redirect: " + errorMsg);
					}
					redir = true;
					c = target.openConnection();
					System.out.println("Followed redirect to " + target);
					redirects++;
				}
			}
		} while (redir);
		return in;
	}

	String getFromLocalJson(String jsonPath) throws FileNotFoundException, IOException {
		File file = new File(jsonPath);
		System.out.println("Requesting content of local JSON file from " + file.getAbsolutePath());
		FileInputStream fis = new FileInputStream(file);
		BufferedReader buff = new BufferedReader(new InputStreamReader(fis, StandardCharsets.UTF_8));

		StringBuffer text = new StringBuffer();

		String line = new String();
		while (true) {
			line = buff.readLine();
			if (line == null)
				break;
			text.append(line + "\n");
		}
		buff.close();
		return text.toString();
	}%>

<%
	Tasks tasks = new Tasks();
	Map<String, Worker> currentWorker = new HashMap<>();
	Map<String, ArrayList<WebToolchain>> toolchains = Tasks.getActiveToolchains();
	Map<String, Worker> worker = Tasks.getWorker();
	Map<Tasks.TaskNames, ArrayList<Example>> examples = Example.getExamples();

	/*
	 *
	 * setting request variables
	 *
	 */
	int s = PageContext.SESSION_SCOPE;
	String tool = request.getParameter("tool");
	String task = request.getParameter("task");
	String ui = request.getParameter("ui");
	Boolean noUI = (null == ui || ui.isEmpty());

	tool = (null == tool) ? "" : tool;
	task = (null == task) ? "" : task;
	ui = noUI ? "home" : ui;

	/*
	 *
	 * request exception handling
	 *
	 */
	// if no tool is requested, opt in all tools
	Boolean showAll = (!ui.equals("home")) && ( tool.isEmpty() || null == worker.get(tool));
	Boolean multipleTools = worker.size() > 1;
	Boolean multipleTasks = (worker.containsKey(tool) && worker.get(tool).getToolchains().size() > 1);

	// redirect unspecified tool-page to home-page
	if (ui.equals("tool") && multipleTools && showAll) {
		response.sendRedirect(request.getContextPath() + "/");
	}

	// handling invalid worker names
	if (worker.containsKey(tool)) {
		currentWorker.put(tool, worker.get(tool));
	} else {
		currentWorker = worker;
	}

	/*
	 * fetching JSON data as tool-page
	 */

	String str = "";

	try {
		if (ui.equals("home")) {
			str = getFromLocalJson(request.getServletContext().getRealPath("/json/home.json"));
		} else if (ui.equals("tool") && worker.containsKey(tool)
				&& !(null == worker.get(tool).getContentURL() || worker.get(tool).getContentURL().isEmpty())) {
			// getting tool page URL from worker
			str = getData(worker.get(tool).getContentURL());
		} else {
			str = getFromLocalJson(request.getServletContext().getRealPath("/json/" + tool + ".json"));
		}
	} catch (Exception e) {
		System.out.println("Exception while retrieving data for " + ui + ":");
		System.out.println(e);
		str = "{ \"description\": \"Error fetching JSON.  (for " + ui + ")\" }";
	}

	JSONObject jsonObject = (JSONObject) JSONValue.parse(str); // for { a: {}, b: {} } JSONs (Object)

	/*
	 *
	 * setting session variables
	 *
	 */
	pageContext.setAttribute("tasks", tasks);
	pageContext.setAttribute("worker", worker, s);
	pageContext.setAttribute("currentWorker", currentWorker, s);
	pageContext.setAttribute("examples", examples, s);
	pageContext.setAttribute("toolchains", toolchains);
	pageContext.setAttribute("showAll", showAll);
	pageContext.setAttribute("ui", ui);
	pageContext.setAttribute("tool", tool, s);
	pageContext.setAttribute("task", task);
	pageContext.setAttribute("multipleTools", multipleTools);
	pageContext.setAttribute("multipleTasks", multipleTasks);
	pageContext.setAttribute("content", jsonObject, s);
%>
<%@ page language="java" contentType="text/html; charset=UTF-8"
	pageEncoding="UTF-8"%>
<!DOCTYPE html PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN" "http://www.w3.org/TR/html4/loose.dtd">
<html>
<head>
<meta http-equiv="Content-Type" content="text/html; charset=UTF-8" />
<meta name="author"
	content="Markus Lindenmann, Oleksii Saukh, Stefan Wissert, German Fordinal" />
<meta name="viewport" content="initial-scale=.6, user-scalable=no" />

<link rel="shortcut icon" type="image/x-icon" href="./favicon.ico">
<link rel="stylesheet" type="text/css" media="screen, projection"
	href="./css/basics.css" charset="utf-8">
<link rel="stylesheet" type="text/css" media="screen, projection"
	href="./css/toast.css" charset="utf-8">
<link rel="stylesheet" type="text/css" media="screen, projection"
	href="font/stylesheet.css" charset="utf-8">


<script type="text/javascript" charset="utf-8" src="./js/jquery.min.js"></script>
<script type="text/javascript" charset="utf-8" src="./js/md5.js"></script>
<script type="text/javascript" charset="utf-8"
	src="./js/transfer.jsp?tool=<c:out value="${tool}" default=""/>"></script>
<script type="text/javascript" charset="utf-8" src="./js/ace-min/ace.js"></script>
<script>
	window.define = ace.define;
	window.require = ace.require;
</script>
<script type="text/javascript" charset="utf-8" src="./js/tools.js"></script>
<script type="text/javascript" charset="utf-8" src="./js/main.js"></script>
<script type="text/javascript" charset="utf-8" src="./js/control.js"></script>
<script type="text/javascript" charset="utf-8" src="./js/dropdown.js"></script>
<script type="text/javascript" charset="utf-8" src="./js/toast.js"></script>

<title>Uni-Freiburg : SWT - Ultimate</title>
</head>
<body
	class="<%=ui%><c:if test="${content.animate ne null && content.animate eq 'true'}"> animate</c:if> horizontal">
	<div id="header"
		class="line-horizontal<c:if test="${ui ne 'int'}"> fixed</c:if>">
		<div class="left">
			<div id="brand-holder">
				<div id="brand-logo"></div>
				<c:choose>
					<c:when test="${ui eq 'home'}">
						<div id="brand-label">ULTIMATE</div>
					</c:when>
					<c:otherwise>
						<a href="./" id="brand-label">ULTIMATE</a>
					</c:otherwise>
				</c:choose>
			</div>
			<c:if test="${ui ne 'home'}">
				<c:choose>
					<c:when test="${showAll && multipleTools}">
						<div class="tool int button spinner visible breadcrumb" id="tool"
							data-default-val="choose tool">
							<div class="label">choose tool</div>
							<div class="box font-average">
								<c:forEach items="${worker}" var="w">
									<div id="<c:out value="${w.value.getId()}" />">
										<c:out value="${w.value.getName()}" />
									</div>
								</c:forEach>
							</div>
						</div>
					</c:when>
					<c:otherwise>
						<div class="tool int breadcrumb selection" id="tool">
							<a href="?ui=tool&tool=<c:out value="${tool}" />"
								class="label selected"
								id="<c:out value="${worker.get(tool).getId()}" />"> <c:out
									value="${worker.get(tool).getName()}" />
							</a>
						</div>
					</c:otherwise>
				</c:choose>
			</c:if>
			<c:if test="${ui eq 'int'}">
				<c:choose>
					<c:when test="${multipleTasks}">
						<div class="int breadcrumb button spinner visible font-light"
							id="task" data-default-val="choose language">
							<div class="label">choose language</div>
							<div class="box font-average">
								<c:forEach items="${worker.get(tool).getToolchains()}" var="tc">
									<div id="<c:out value="${tc.getId()}" />"
										<c:if test="${task eq tc.getId()}"> class="selected"</c:if>>
										<c:out value="${tc.getLanguage()}" />
									</div>
								</c:forEach>
							</div>
						</div>
					</c:when>
					<c:when test="${showAll && multipleTools}">
						<div class="int breadcrumb button spinner visible font-light"
							id="task" style="display: none;"
							data-default-val="choose language">
							<div class="label">choose language</div>
							<div class="box font-average"></div>
						</div>
					</c:when>
					<c:otherwise>
						<div class="int breadcrumb spinner visible font-light selection"
							id="task" data-default-val="choose language">
							<c:set value="${worker.get(tool).getToolchains()[0]}" var="tc" />
							<div class="label selected" id="<c:out value="${tc.getId()}" />">
								<c:out value="${tc.getLanguage()}" />
							</div>
							<div class="box font-average"></div>
						</div>
					</c:otherwise>
				</c:choose>
			</c:if>
		</div>
		<div class="right">
			<c:if test="${ui eq 'tool'}">
				<div class="tool" id="tool-logo"
					style="background-image:url(<c:out value="${worker.get(tool).getLogoURL()}" />);"></div>
			</c:if>
			<c:if test="${ui eq 'int'}">
				<div class="int button selection spinner hidden line-left"
					id="samples" data-default-val="samples">
					<div class="label">samples</div>
					<div class="img"></div>
					<div class="box font-average"></div>
				</div>
				<div class="int button line-left" id="play"
					data-default-val="evaluate">
					<div class="label">execute</div>
					<div class="img">
						<div class="ajax-loader"></div>
					</div>
				</div>
				<div class="int button menu line-left" id="settings"
					data-default-val="settings">
					<div class="label">settings</div>
					<div class="img"></div>
					<div class="box font-average"></div>
				</div>
			</c:if>
		</div>
		<div id="info-bar" class="line-top">
			<div id="info-label" class="font-normal color-lighter"></div>
			<div class="hide">
				<div class="tooltip">
					<div></div>
					<label>remind</label>
				</div>
			</div>
			<div class="close">
				<div class="tooltip">
					<div></div>
					<label>close</label>
				</div>
			</div>
		</div>
		<div class="shadow down"></div>
	</div>


	<div id="content" class="no-messages">

		<c:if test="${ui ne 'int'}">
			<!-- CONTENT (HOME, TOOL) -->
			<div class="<%=ui%> section link-emph">
				<div class="caption">description</div>
				<div class="text font-normal color-lighter">
					<c:out value="${content.description}"
						escapeXml="${!(content.html ne null && content.html eq 'true')}" />
				</div>
			</div>
			<c:if test="${ui eq 'home'}">
				<!-- HOME -->
				<div class="home section wide">
					<div class="caption">tools</div>
					<div class="toolchains" id="toolchains">
						<c:forEach items="${worker}" var="w">
							<div class="toolchain line-right">
								<div class="toolchain-name font-normal">
									<a href="?ui=tool&tool=<c:out value="${w.value.getId()}" />">ULTIMATE
										<c:out value="${w.value.getName()}" />
									</a>
								</div>
								<div class="toolchain-description font-average">
									<div>Description</div>
									<div class="color-lighter">
										<c:out value="${w.value.getDescription()}" />
									</div>
								</div>
								<div class="toolchain-description font-average">
									<div>Language</div>
									<div class="color-lighter">
										<c:forEach items="${w.value.getLanguages()}" var="lang">
											<span><c:out value="${lang}" /></span>
										</c:forEach>
									</div>
								</div>
								<div class="toolchain-buttons font-normal color-lighter">
									<a href="?ui=int&tool=<c:out value="${w.value.getId()}" />">Try
										online</a> <a
										href="?ui=tool&tool=<c:out value="${w.value.getId()}" />"
										class="no-border">Read more</a>
								</div>
							</div>
						</c:forEach>
					</div>
				</div>
			</c:if>
			<!-- Generating all sections from JSON file -->
			<c:forEach items="${content.sections}" var="section">
				<div
					class="<c:out value="${ui}" /> section<c:if 
                         test="${section.link_deco ne null && section.link_deco eq 'true'}"> link-emph</c:if><c:if 
                         test="${section.flip ne null && section.flip eq 'true'}"> flip</c:if>">
					<div class="caption">
						<c:out value="${section.title}" />
					</div>
					<c:choose>
						<c:when test="${section.type eq 'text' || section.type eq 'html'}">
							<div class="text font-normal color-lighter">
								<c:out value="${section.content}"
									escapeXml="${!(section.html ne null && section.html eq 'true')}" />
							</div>
						</c:when>
						<c:when test="${section.type eq 'list'}">
							<c:if test="${section.content ne null}">
								<div class="text font-normal color-lighter">
									<c:out value="${section.content}"
										escapeXml="${!(section.html ne null && section.html eq 'true')}" />
								</div>
							</c:if>
							<ul class="text font-normal color-lighter">
								<c:forEach items="${section.list}" var="li">
									<li><c:out value="${li}"
											escapeXml="${!(section.html ne null && section.html eq 'true')}" />
									</li>
								</c:forEach>
							</ul>
						</c:when>
						<c:when test="${section.type eq 'interface'}">
							<div class="text interface font-normal color-lighter">
								<div class="img interface-screenshot"></div>
								<c:out value="${section.content}"
									escapeXml="${!(section.html ne null && section.html eq 'true')}" />
								<div class="toolchain-buttons color-lighter">
									<a href="?ui=int&tool=<c:out value="${param.tool}" />"><c:out
											value="${section.button}">Try now</c:out></a>
								</div>
							</div>
						</c:when>
						<c:otherwise>
              Sections with type "<c:out value="${section.type}" />" not supported yet.
            </c:otherwise>
					</c:choose>
				</div>
			</c:forEach>
		</c:if>

		<c:if test="${ui eq 'int'}">
			<!-- INTERFACE -->
			<div id="editor" class="int"></div>
			<div id="messages" class="int line">
				<div class="shadow up resize-v"></div>
				<div id="messages-wrapper">
					<div id="messages-head">
						<div id="messages-caption" class="font-bold font-normal">ULTIMATE
							Results</div>
						<div id="messages-actions">
							<div class="hide-msgs mini-button"></div>
							<div class="window mini-button"></div>
						</div>
						<div id="messages-labels" class="font-average">
							<div class="msg-icon"></div>
							<div class="msg-line">Line</div>
							<div class="msg-column">Column</div>
							<div class="msg-description">Description</div>
						</div>
					</div>
				</div>
				<div id="resize-vertical" class="resize-h"></div>
			</div>
			<div id="show-msg" class="int"></div>
		</c:if>

	</div>

</body>
</html>