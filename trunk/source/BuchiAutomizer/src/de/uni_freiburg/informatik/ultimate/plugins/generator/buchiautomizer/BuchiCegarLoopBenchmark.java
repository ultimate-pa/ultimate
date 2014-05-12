package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;

import java.util.ArrayList;
import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopBenchmarkType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.benchmark.IBenchmarkType;

public class BuchiCegarLoopBenchmark extends CegarLoopBenchmarkType implements IBenchmarkType {
	
	private static final BuchiCegarLoopBenchmark s_Instance = new BuchiCegarLoopBenchmark();
	
	public static final String s_NonLiveStateRemoval = "NonLiveStateRemoval";
	public static final String s_BuchiClosure = "BuchiClosure";
	
	public static BuchiCegarLoopBenchmark getInstance() {
		return s_Instance;
	}

	@Override
	public Collection<String> getKeys() {
		ArrayList<String> keyList = new ArrayList<String>(super.getKeys());
		keyList.add(s_NonLiveStateRemoval);
		keyList.add(s_BuchiClosure);
		return keyList;
	}
	
	

}
