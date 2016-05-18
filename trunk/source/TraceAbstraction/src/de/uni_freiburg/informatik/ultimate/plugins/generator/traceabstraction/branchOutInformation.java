package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.List;
import java.util.Map;

public class branchOutInformation
{
	public boolean isBranchIn = false;
	public int positionBranchOut = 0;
	public Map<Integer, List<Integer>> informationFromCFG;
}
