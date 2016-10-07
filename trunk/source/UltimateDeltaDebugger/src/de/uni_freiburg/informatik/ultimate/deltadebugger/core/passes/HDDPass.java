package de.uni_freiburg.informatik.ultimate.deltadebugger.core.passes;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.PassDescription;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd.DefaultStrategy;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd.HDDGeneratorFactory;

/**
 * HDD default Passes
 */
public class HDDPass {

	/**
	 * Single-Pass HDD algorithm (without reparsing between levels)
	 */
	public static final PassDescription DEFAULT = PassDescription
			.builder((new HDDGeneratorFactory(new DefaultStrategy(), false))::analyze).name("HDD")
			.description("Hiearchical Delta-Debugging inspired pass without reparsing between levels").build();


	/**
	 * Single-Pass HDD algorithm (with reparsing between levels)
	 */
	public static final PassDescription REPARSING = PassDescription
			.builder((new HDDGeneratorFactory(new DefaultStrategy(), true))::analyze).name("HDD (Reparsing)")
			.description("Hiearchical Delta-Debugging inspired pass with reparsing between levels").build();

	
	/**
	 * Repeat until no redcution is possible (HDD*)
	 */
	public static final PassDescription HDDSTAR = DEFAULT.copy().repeatUntilReductionFails(true).build();
	
	private HDDPass() {
	}

}
