package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Consumer;

/**
 * Measures speed of different closures on random generated matrices.
 *
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class ClosureSpeedTest {

	// -XX:+PrintCompilation -verbose:gc
	// -XX:-BackgroundCompilation
	public static void main(String[] args) {
		final ClosureSpeedTest st = new ClosureSpeedTest();
		st.addWarmUp(20, 3000);
		st.addTest(20, 8000);
		st.addTest(50, 600);
		st.addTest(100, 80);
		st.addTest(150, 20);
		st.addFunction("naiv", OctMatrix::shortestPathClosureNaiv);
		st.addFunction("apron", OctMatrix::shortestPathClosureApron);
		st.addFunction("fsparse", OctMatrix::shortestPathClosureFullSparse);
		st.addFunction("sparse", OctMatrix::shortestPathClosureSparse);
		st.addFunction("psparse", OctMatrix::shortestPathClosurePrimitiveSparse);
		st.run();
	}

	private static class Scenario {
		int vars;
		int cycles;
		boolean warmup;
	}
	
	private static class Function {
		String name;
		Consumer<OctMatrix> function;
		/** Measured time in ns from last scenario. */
		long measuredNanoSeconds;
	}

	private final List<Scenario> mScenarios = new ArrayList<>();
	private final List<Function> mFunctions = new ArrayList<>();
	
	public void addWarmUp(int variables, int cycles) {
		final Scenario s = new Scenario();
		s.vars = variables;
		s.cycles = cycles;
		s.warmup = true;
		mScenarios.add(s);
	}

	public void addTest(int variables, int cycles) {
		final Scenario s = new Scenario();
		s.vars = variables;
		s.cycles = cycles;
		s.warmup = false;
		mScenarios.add(s);
	}

	
	public void addFunction(String name, Consumer<OctMatrix> function) {
		final Function f = new Function();
		f.name = name;
		f.function = function;
		mFunctions.add(f);
	}
	
	public void run() {
		printTableHeader();
		printTableRule();
		for (final Scenario s : mScenarios) {
			printCurrentTableRowLeft(s);		
			runScenario(s);
			printCurrentTableRowRight(s);
		}
	}

	private void runScenario(Scenario scenario) {
		resetMeassuredNanoSeconds();
		for (int mi = 0; mi < scenario.cycles; ++mi) {
			final OctMatrix mOrig = OctMatrix.random(scenario.vars);
			for (final Function f : mFunctions) {
				final OctMatrix m = mOrig.copy();
				final long tStart = System.nanoTime();
				f.function.accept(m);
				f.measuredNanoSeconds += System.nanoTime() - tStart;		
			}
		}
	}
	
	private void resetMeassuredNanoSeconds() {
		for (final Function f : mFunctions) {
			f.measuredNanoSeconds = 0;
		}
	}
	
	private void printTableHeader() {
		System.out.print("vars | cycles |" );
		for (final Function f : mFunctions) {
			System.out.format(" | %8s", f.name);
		}
		System.out.println();
	}

	private void printTableRule() {
		System.out.print("-----+--------+");
		for (int i = 0; i < mFunctions.size(); ++i) {
			System.out.print("-+---------");
		}
		System.out.println();
	}
	
	private void printCurrentTableRowLeft(Scenario s) {
		System.out.format("% 4d | %6d |", s.vars, s.cycles);
	}

	private void printCurrentTableRowRight(Scenario s) {
		for (final Function f : mFunctions) {
			if (s.warmup) {
				System.out.format(" |  warm-up");				
			} else {
				System.out.format(" | %6.1f s", f.measuredNanoSeconds * 1e-9);				
			}
		}
		System.out.println();
	}

}
