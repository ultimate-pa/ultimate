/**
 * 
 */
package jayhorn;

import jayhorn.soot.SootRunner.CallgraphAlgorithm;
import jayhorn.soot.SootToCfg;

public class Main {

	public static void main(String[] args) {
		String javaInput = "";
		String classPath = "";
		if (args.length > 0) {
			javaInput = args[0];
			if (args.length > 1) {
				classPath = args[1];
			}
			SootToCfg soot2cfg = new SootToCfg();
			soot2cfg.run(javaInput, classPath, CallgraphAlgorithm.None);
		} else {
			System.err.println("usage: [class_dir/jar_file] [(optional)classpath]");
		}
	}
}