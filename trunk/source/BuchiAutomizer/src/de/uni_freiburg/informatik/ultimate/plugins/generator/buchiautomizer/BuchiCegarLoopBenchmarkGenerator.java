package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;

import java.util.ArrayList;
import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopBenchmarkGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.benchmark.IBenchmarkType;

public class BuchiCegarLoopBenchmarkGenerator extends CegarLoopBenchmarkGenerator {
	
	@Override
	public IBenchmarkType getBenchmarkType() {
		return BuchiCegarLoopBenchmark.getInstance();
	}

	@Override
	public String[] getStopwatches() {
		ArrayList<String> al = new ArrayList<String>();
		al.addAll(Arrays.asList(super.getStopwatches()));
		al.add(BuchiCegarLoopBenchmark.s_NonLiveStateRemoval);
		al.add(BuchiCegarLoopBenchmark.s_BuchiClosure);
		return al.toArray(new String[0]);
	}
	
	

}
