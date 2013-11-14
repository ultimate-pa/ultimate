package system;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FilenameFilter;
import java.net.URISyntaxException;
import java.net.URL;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.ParseEnvironment;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.TestCaseWithLogger;

public class SystemTest extends TestCaseWithLogger {

	public void testSystem() throws URISyntaxException, FileNotFoundException {
		String name = getClass().getPackage().getName();
		URL url = getClass().getClassLoader().getResource(name);
		File f = new File(url.toURI());
		File[] lst = f.getParentFile().getParentFile().listFiles(
				new FilenameFilter() {
			
			@Override
			public boolean accept(File dir, String name) {
				return name.equals("test");
			}
		});
		if (lst == null || lst.length != 1)
			return;
		File testDir = lst[0];
		lst = testDir.listFiles();
		for (File dir : lst) {
			for (File tst: dir.listFiles(new FilenameFilter() {
				
				@Override
				public boolean accept(File dir, String name) {
					return name.endsWith(".smt2") && 
							!name.endsWith(".msat.smt2");
				}
			})) {
				try {
					if (shouldExecute(tst))
						performTest(tst);
				} catch (SMTLIBException se) {
					fail("File " + tst.getAbsolutePath() + " produced error:\n"
							+ se.getMessage());
				}
			}
		}
	}
	
	private void performTest(File f) throws SMTLIBException, FileNotFoundException {
		System.out.println("Testing " + f.getAbsolutePath());
		SMTInterpol solver = new SMTInterpol(Logger.getRootLogger(), false);
		ParseEnvironment pe = new ParseEnvironment(solver);
		pe.parseStream(new FileReader(f), "TestStream");
	}
	
	private boolean shouldExecute(File f) {
		String fname = f.getName();
		if (fname.startsWith("tightrhombus")) {
			String sizestr = fname.substring(fname.lastIndexOf('-') + 1,
					fname.lastIndexOf('.'));
			int size = Integer.parseInt(sizestr);
			return size < 5;
		}
		return true;
	}
	
}
