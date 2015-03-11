package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.witnesschecking;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.InterproceduralSequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ParallelComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessEdge;

public class WitnessAutomatonLetter {
	WitnessEdge m_WitnessEdge;
	
	public WitnessAutomatonLetter(WitnessEdge we) {
		m_WitnessEdge = we;
	}
	
	public boolean isPureAssumptionEdge() {
		return m_WitnessEdge.getLocation().getStartLine() == -1;
	}
	
	public boolean isProbalyDeclaration() {
		return m_WitnessEdge.getSourceCode().contains("int");
	}
	
	public int getLineNumber() {
		return m_WitnessEdge.getLocation().getStartLine();
	}





	@Override
	public String toString() {
		return m_WitnessEdge.toString();
	}
	
	

}
