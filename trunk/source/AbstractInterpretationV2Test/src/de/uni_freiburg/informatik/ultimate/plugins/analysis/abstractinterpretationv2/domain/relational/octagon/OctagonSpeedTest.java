package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.function.Consumer;

import org.junit.Assert;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon.OctMatrix;

public class OctagonSpeedTest {

	// -XX:+PrintCompilation -verbose:gc
	// -XX:-BackgroundCompilation
	public static void main(String[] args) {
		OctagonSpeedTest st = new OctagonSpeedTest();
		st.addWarmUp(20, 3000);
		st.addTest(20, 5000);
		st.addTest(50, 600);
		st.addTest(100, 100);
		st.addTest(150, 10);
		st.addFunction("naiv", OctMatrix::strongClosureNaiv);
		st.addFunction("apron", OctMatrix::strongClosureApron);
		st.addFunction("fsparse", OctMatrix::strongClosureFullSparse);
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

	private List<Scenario> mScenarios = new ArrayList<>();
	private List<Function> mFunctions = new ArrayList<>();
	
	public void addWarmUp(int variables, int cycles) {
		Scenario s = new Scenario();
		s.vars = variables;
		s.cycles = cycles;
		s.warmup = true;
		mScenarios.add(s);
	}

	public void addTest(int variables, int cycles) {
		Scenario s = new Scenario();
		s.vars = variables;
		s.cycles = cycles;
		s.warmup = false;
		mScenarios.add(s);
	}

	
	public void addFunction(String name, Consumer<OctMatrix> function) {
		Function f = new Function();
		f.name = name;
		f.function = function;
		mFunctions.add(f);
	}
	
	public void run() {
		printTableHeader();
		printTableRule();
		for (Scenario s : mScenarios) {
			printCurrentTableRowLeft(s);		
			runScenario(s);
			printCurrentTableRowRight(s);
		}
	}

	private void runScenario(Scenario scenario) {
		resetMeassuredNanoSeconds();
		for (int mi = 0; mi < scenario.cycles; ++mi) {
			OctMatrix m = OctMatrix.random(scenario.vars);
			for (Function f : mFunctions) {
				long tStart = System.nanoTime();
				f.function.accept(m);
				f.measuredNanoSeconds += System.nanoTime() - tStart;		
			}
		}
	}
	
	private void resetMeassuredNanoSeconds() {
		for (Function f : mFunctions) {
			f.measuredNanoSeconds = 0;
		}
	}
	
	private void printTableHeader() {
		System.out.print("vars | cycles |" );
		for (Function f : mFunctions) {
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
		for (Function f : mFunctions) {
			if (s.warmup) {
				System.out.format(" |  warm-up");				
			} else {
				System.out.format(" | %6.1f s", f.measuredNanoSeconds * 1e-9);				
			}
		}
		System.out.println();
	}

}
