<%@ page language="java" contentType="application/json; charset=UTF-8"
	pageEncoding="UTF-8"%>
<%@ taglib prefix="c" uri="http://java.sun.com/jsp/jstl/core"%>
<c:if test="${param.ui eq 'home'}">
{
  "id": "home",
  "description": "Here goes the description, could you think!",
  "user_info": "JSON: defined in Website/json.jsp",
  "animate": "false",
  "html": "false",
  "sections":
  [
    {
      "title": "title1",
      "type": "text",
      "html": "false",
      <%-- type can be one of: text, image, html, list, interface. --%>
      "content": "So here is, what should be standing in the description",
      "content (list)":
      [
        "first list element",
        "second list element",
        "third list element",
        "fourth list element"
      ],
      "link": "http://www.google.com",
      "link_deco": "false"
    },
    {
      "title": "some list",
      "type": "list",
      "html": "true",
      "content":
      [
        "first list element",
        "second list element",
        "third list element",
        "fourth list element",
        "<a href=\"http://swt.informatik.uni-freiburg.de/staff/christian_schilling\">Christian
		Schilling</a>",
      ],
      "link_deco": "false"
    },
    {
      "title": "web interface",
      "type": "interface",
      "html": "false",
      "content": "Not very much information to this specific point of literation!",
      "link_deco": "false",
      "button": "Try online interface",
      "flip": "true"
    },
    {
      "title": "developer",
      "type": "text",
      "html": "true",
      "content": "Alex Saukh (web interface, CDT interface, CACSL2Boogie, Büchi minimization)<br>Arend v. Reinersdorff (predecessor of ULTIMATE)<br>Betim Musa (automata script, interpolants from unsatisfiable cores)<br>Björn Buchhold (predecessor of ULTIMATE, the 2.0 version)<br>Chen Kefei (nested interpolants)<br>Christian Ortolf (predecessor of ULTIMATE)<br>
	<a href=\"http://swt.informatik.uni-freiburg.de/staff/christian_schilling\">Christian
		Schilling</a> (NWA minimization)<br>Christian Simon (predecessor of ULTIMATE, the 2.0 version)<br>Christoph Hofmann (Ultimate in the cloud)<br>
	<a href=\"http://swt.informatik.uni-freiburg.de/staff/dietsch\">Daniel
		Dietsch</a>
	<br>Daniel Christiany (NWA)<br>
	<a href=\"http://swt.informatik.uni-freiburg.de/staff/ermis\">Evren
		Ermis</a>
	<br>Fabian Reiter (Büchi complementation)<br>Jan Leike (NWA, <a
		href=\"http://ultimate.informatik.uni-freiburg.de/LassoRanker/\">LassoRanker</a>)<br>Jan Hättig (total interpolation)<br>Jan Mortensen (NWA, petri nets)<br>Jelena Barth (Jung visualization)<br>Jeremi Dzienian (Temporal Properties)<br>Julian Jarecki (petri nets)<br>
	<a href=\"http://swt.informatik.uni-freiburg.de/staff/hoenicke\">Jochen
		Hoenicke</a>
	<br>
	<a href=\"http://swt.informatik.uni-freiburg.de/staff/christ\">Jürgen
		Christ</a>
	<br>Justus Bisser<br>Markus Lindenmann (web interface, CDT interface, CACSL2Boogie, Büchi minimierung, C memory model)<br>Markus Pomrehn (formula simplification, alternating automata)<br>Markus Zeiger (NWA, E-Matching)<br>
	<a href=\"http://swt.informatik.uni-freiburg.de/staff/greitschus\">Marius
		Greitschus</a>
	<br>
	<a href=\"http://swt.informatik.uni-freiburg.de/staff/heizmann\">Matthias
		Heizmann</a>
	<br>Matthias Keil (Prefuse visualization)<br>Nicola Sheldrick (predecessor of ULTIMATE)<br>Robert Jakob (predecessor of ULTIMATE)<br>Simon Ley (IC3)<br>Stefan Wissert (Web interface, CDT interface, CACSL2Boogie, IValuations, large block encoding)<br>Vincent Langenfeld (Temporal Properties, LTL software model checking)<br>Xiaolin Wu (emptiness check for Büchi nested word automata) ",
      "link_deco": "true"
    },
    {
      "title": "dependencies",
      "type": "text",
      "html": "true",
      "content": "Many plugins in <span style="""font-variant:small-caps\">Ultimate</span> require an <a
		href=\"http://smtlib.org/SMT-LIB\">SMT-LIB</a> compatible theorem prover. We use <a
		href=\"http://ultimate.informatik.uni-freiburg.de/smtinterpol/\">SMTInterpol</a>.<br>
	<br>Ultimate uses <a href=\"http://wiki.eclipse.org/index.php/Rich_Client_Platform\">Eclipse
		RCP</a>. Plugins that handle C code depend on <a href=\"http://www.eclipse.org/cdt/\">Eclipse
		CDT</a>.",
      "link_deco": "true"
    }
  ]
}
</c:if>
<c:if test="${param.ui eq 'tool' || param.tool eq 'Automata Script'}">
{
  "id": "<c:out value="${param.tool}" />",
  "description": "Tool page!",
  "user_info": "No cookies used so far!",
  "animate": "true",
  "sections":
  [
    {
      "title": "title1",
      "type": "text",
      "html": "false",
      <%-- type can be one of: text, image, html, list, interface. --%>
      "content": "So here is, what should be standing in the description",
      "content (list)":
      [
        "first list element",
        "second list element",
        "third list element",
        "fourth list element"
      ],
      "link": "http://www.google.com",
      "link_deco": "false"
    },
    {
      "title": "some list",
      "type": "list",
      "html": "true",
      "content":
      [
        "first list element",
        "second list element",
        "third list element",
        "fourth list element",
        "<a href=\"http://swt.informatik.uni-freiburg.de/staff/christian_schilling\">Christian
		Schilling</a>",
      ],
      "link_deco": "false"
    },
    {
      "title": "web interface",
      "type": "interface",
      "html": "false",
      "content": "Not very much information to this specific point of literation!",
      "link_deco": "false",
      "button": "Try online interface"
    },
    {
      "title": "developer",
      "type": "text",
      "html": "true",
      "content": "Alex Saukh (web interface, CDT interface, CACSL2Boogie, Büchi minimization)<br>Arend v. Reinersdorff (predecessor of ULTIMATE)<br>Betim Musa (automata script, interpolants from unsatisfiable cores)<br>Björn Buchhold (predecessor of ULTIMATE, the 2.0 version)<br>Chen Kefei (nested interpolants)<br>Christian Ortolf (predecessor of ULTIMATE)<br>
	<a href=\"http://swt.informatik.uni-freiburg.de/staff/christian_schilling\">Christian
		Schilling</a> (NWA minimization)<br>Christian Simon (predecessor of ULTIMATE, the 2.0 version)<br>Christoph Hofmann (Ultimate in the cloud)<br>
	<a href=\"http://swt.informatik.uni-freiburg.de/staff/dietsch\">Daniel
		Dietsch</a>
	<br>Daniel Christiany (NWA)<br>
	<a href=\"http://swt.informatik.uni-freiburg.de/staff/ermis\">Evren
		Ermis</a>
	<br>Fabian Reiter (Büchi complementation)<br>Jan Leike (NWA, <a
		href=\"http://ultimate.informatik.uni-freiburg.de/LassoRanker/\">LassoRanker</a>)<br>Jan Hättig (total interpolation)<br>Jan Mortensen (NWA, petri nets)<br>Jelena Barth (Jung visualization)<br>Jeremi Dzienian (Temporal Properties)<br>Julian Jarecki (petri nets)<br>
	<a href=\"http://swt.informatik.uni-freiburg.de/staff/hoenicke\">Jochen
		Hoenicke</a>
	<br>
	<a href=\"http://swt.informatik.uni-freiburg.de/staff/christ\">Jürgen
		Christ</a>
	<br>Justus Bisser<br>Markus Lindenmann (web interface, CDT interface, CACSL2Boogie, Büchi minimierung, C memory model)<br>Markus Pomrehn (formula simplification, alternating automata)<br>Markus Zeiger (NWA, E-Matching)<br>
	<a href=\"http://swt.informatik.uni-freiburg.de/staff/greitschus\">Marius
		Greitschus</a>
	<br>
	<a href=\"http://swt.informatik.uni-freiburg.de/staff/heizmann\">Matthias
		Heizmann</a>
	<br>Matthias Keil (Prefuse visualization)<br>Nicola Sheldrick (predecessor of ULTIMATE)<br>Robert Jakob (predecessor of ULTIMATE)<br>Simon Ley (IC3)<br>Stefan Wissert (Web interface, CDT interface, CACSL2Boogie, IValuations, large block encoding)<br>Vincent Langenfeld (Temporal Properties, LTL software model checking)<br>Xiaolin Wu (emptiness check for Büchi nested word automata) ",
      "link_deco": "true"
    },
    {
      "title": "dependencies",
      "type": "text",
      "html": "true",
      "content": "Many plugins in <span style="""font-variant:small-caps\">Ultimate</span> require an <a
		href=\"http://smtlib.org/SMT-LIB\">SMT-LIB</a> compatible theorem prover. We use <a
		href=\"http://ultimate.informatik.uni-freiburg.de/smtinterpol/\">SMTInterpol</a>.<br>
	<br>Ultimate uses <a href=\"http://wiki.eclipse.org/index.php/Rich_Client_Platform\">Eclipse
		RCP</a>. Plugins that handle C code depend on <a href=\"http://www.eclipse.org/cdt/\">Eclipse
		CDT</a>.",
      "link_deco": "true"
    }
  ]
}
</c:if>