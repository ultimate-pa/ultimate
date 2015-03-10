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


	public boolean isCompatible(CodeBlock cb) {
		if (cb instanceof Call) {
			Call call = (Call) cb;
			return isCompatible(call);
		} else if (cb instanceof InterproceduralSequentialComposition) {
			InterproceduralSequentialComposition isc = (InterproceduralSequentialComposition) cb;
			return isCompatible(isc);
		} else if (cb instanceof ParallelComposition) {
			ParallelComposition pc = (ParallelComposition) cb;
			return isCompatible(pc);
		} else if (cb instanceof Return) {
			Return ret = (Return) cb;
			return isCompatible(ret);
		} else if (cb instanceof SequentialComposition) {
			SequentialComposition sc = (SequentialComposition) cb;
			return isCompatible(sc);
		} else if (cb instanceof StatementSequence) {
			StatementSequence ss = (StatementSequence) cb;
			return isCompatible(ss);
		} else {
			throw new AssertionError("unknown type of CodeBlock");
		}
	}

	
	boolean isCompatible(Call call) {
		return isCompatible(call.getCallStatement());
	}
	
	boolean isCompatible(InterproceduralSequentialComposition isc) {
		for (CodeBlock cb : isc.getCodeBlocks()) {
			if (isCompatible(cb)) {
				return true;
			}
		}
		return false;
	}
	


	boolean isCompatible(ParallelComposition pc) {
		for (CodeBlock cb : pc.getCodeBlocks()) {
			if (isCompatible(cb)) {
				return true;
			}
		}
		return false;
	}
	
	boolean isCompatible(Return ret) {
		return isCompatible(ret.getPayload().getLocation());
	}
	
	boolean isCompatible(SequentialComposition sc) {
		for (CodeBlock cb : sc.getCodeBlocks()) {
			if (isCompatible(cb)) {
				return true;
			}
		}
		return false;
	}
	
	boolean isCompatible(StatementSequence ss) {
		for (Statement st : ss.getStatements()) {
			if (isCompatible(st)) {
				return true;
			}
		}
		return false;
	}
	
	boolean isCompatible(Statement st) {
		return isCompatible(st.getLocation());
	}
	
	

	private boolean isCompatible(ILocation location) {
		int witnessLine = m_WitnessEdge.getLocation().getStartLine();
		return (location.getStartLine() <= witnessLine && location.getEndLine() >= witnessLine);
	}


	@Override
	public String toString() {
		return m_WitnessEdge.toString();
	}
	
	

}
