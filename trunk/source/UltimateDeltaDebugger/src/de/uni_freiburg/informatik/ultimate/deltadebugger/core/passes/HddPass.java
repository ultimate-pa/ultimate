package de.uni_freiburg.informatik.ultimate.deltadebugger.core.passes;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.PassDescription;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd.AggressiveStrategy;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd.HddGeneratorFactory;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd.IHddStrategy;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd.SafeStrategy;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd.UnreferencedStrategy;

/**
 * HDD default Passes.
 */
public final class HddPass {

	public static final IHddStrategy AGGRESSIVE_STRATEGY = new AggressiveStrategy();
	public static final IHddStrategy SAFE_STRATEGY = new SafeStrategy();
	public static final IHddStrategy UNREFERENCED_STRATEGY = new UnreferencedStrategy();

	public static final IHddStrategy DEFAULT_STRATEGY = AGGRESSIVE_STRATEGY;

	/**
	 * Single-Pass HDD algorithm (without reparsing between levels).
	 */
	public static final PassDescription DEFAULT = PassDescription
			.builder(new HddGeneratorFactory(DEFAULT_STRATEGY, false)::analyze).name("HDD")
			.description("Hiearchical Delta-Debugging inspired pass without reparsing between levels").build();

	/**
	 * Single-Pass HDD algorithm (with reparsing between levels).
	 */
	public static final PassDescription REPARSING = PassDescription
			.builder(new HddGeneratorFactory(DEFAULT_STRATEGY, true)::analyze).name("HDD (Reparsing)")
			.description("Hiearchical Delta-Debugging inspired pass with reparsing between levels").build();

	/**
	 * Repeat until no redcution is possible (HDD*).
	 */
	public static final PassDescription HDDSTAR = DEFAULT.copy().repeatUntilReductionFails(true).build();

	private HddPass() {
	}
}
