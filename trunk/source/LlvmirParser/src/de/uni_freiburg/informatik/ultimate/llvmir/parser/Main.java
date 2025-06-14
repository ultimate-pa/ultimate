package de.uni_freiburg.informatik.ultimate.llvmir.parser;

import java.io.File;
import java.io.IOException;

public class Main {
	public static void main(final String[] args) throws IOException, InterruptedException {
		final UltimateLlvmirParser parser = new UltimateLlvmirParser();
		parser.init();

		final File[] files = parser
				.parseable(new File[] { new File("ACSL-referring_to_global_var_from_function_scope_opt.ll") });
		parser.parseAST(files);
	}

}
