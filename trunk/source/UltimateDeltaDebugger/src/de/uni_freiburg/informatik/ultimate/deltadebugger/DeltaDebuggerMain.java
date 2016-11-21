package de.uni_freiburg.informatik.ultimate.deltadebugger;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.DefaultPassContext;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.IPassContext;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.DefaultParserWithACSL;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util.PSTPrintVisitor;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceDocument;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.StringSourceDocument;
import de.uni_freiburg.informatik.ultimate.test.ConsoleLogger;

public class DeltaDebuggerMain {

	public static void main(String[] args) throws IOException {
		
		//String inputFilePath = "C:\\bscthesis\\code\\ultimate\\ultimate\\trunk\\examples\\CToBoogieTranslation\\regression\\switchHard.c";
		//String inputFilePath = "C:\\Users\\Admin\\Downloads\\Firefox\\frama-c-Aluminium-20160502\\tests\\bugs\\evoting.c";
		//String inputFilePath = "C:\\bscthesis\\code\\ultimate\\ultimate\\trunk\\examples\\rers2016\\slicing\\Problem11\\Problem11-15.c";
		//String inputFilePath = "C:\\bscthesis\\code\\cdt-sandbox\\cdt-sandbox.cxx-sources\\vcc_lsearch.c";
		String inputFilePath = "C:\\bscthesis\\code\\cdt-sandbox\\cdt-sandbox.cxx-sources\\hello.c";

		ILogger logger = new ConsoleLogger();

		String inputSource = new String(Files.readAllBytes(Paths.get(inputFilePath)), StandardCharsets.UTF_8);

		ISourceDocument source = new StringSourceDocument(inputSource);

		IPassContext context = new DefaultPassContext(source, new DefaultParserWithACSL(logger, "<input>",
				new String[] { "C:\\bscthesis\\code\\cdt-sandbox\\cdt-sandbox.cxx-sources\\" }, new String[] {}),
				logger);

		context.getSharedPst().accept(new PSTPrintVisitor(s -> System.out.print(s)));

		System.out.println("test");
	}

}
