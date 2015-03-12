package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.witnesschecking;

import java.util.HashSet;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.InterproceduralSequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ParallelComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.util.HashRelation;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessNode;

public class WitnessLocationMatcher {

	private final IUltimateServiceProvider m_Services;
	private final Set<WitnessAutomatonLetter> m_PureAnnotationEdges = new HashSet<WitnessAutomatonLetter>();
	private final HashRelation<Integer, WitnessAutomatonLetter> m_LineNumber2WitnessLetter = new HashRelation<>();
	private final HashRelation<ILocation, WitnessAutomatonLetter> m_SingleLineLocation2WitnessLetters = new HashRelation<>();
	private final HashRelation<WitnessAutomatonLetter, ILocation> m_WitnessLetters2SingleLineLocations = new HashRelation<>();
	private final Set<ILocation> m_MultiLineLocations = new HashSet<ILocation>();
	private final Logger m_Logger;

	public WitnessLocationMatcher(
			IUltimateServiceProvider services,
			INestedWordAutomatonSimple<CodeBlock, IPredicate> controlFlowAutomaton,
			NestedWordAutomaton<WitnessAutomatonLetter, WitnessNode> witnessAutomaton) {
		m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
		partitionEdges(witnessAutomaton.getInternalAlphabet());
		matchLocations(controlFlowAutomaton.getInternalAlphabet());
		matchLocations(controlFlowAutomaton.getCallAlphabet());
		matchLocations(controlFlowAutomaton.getReturnAlphabet());
		HashSet<WitnessAutomatonLetter> unmatchedWitnessLetters = new HashSet<WitnessAutomatonLetter>(witnessAutomaton.getInternalAlphabet());
		unmatchedWitnessLetters.removeAll(m_WitnessLetters2SingleLineLocations.getDomain());
		m_Logger.info(witnessAutomaton.getInternalAlphabet().size() + " witness edges");
		m_Logger.info(m_PureAnnotationEdges.size() + " pure annotation edges");
		m_Logger.info(unmatchedWitnessLetters.size() + " unmatched witness edges");
		m_Logger.info(m_WitnessLetters2SingleLineLocations.getDomain().size() + " matched witness edges");
		m_Logger.info(m_SingleLineLocation2WitnessLetters.getDomain().size() + " single line locations");
		m_Logger.info(m_MultiLineLocations.size() + " multi line locations");
	}

	public boolean isMatchedWitnessEdge(WitnessAutomatonLetter wal) {
		return m_WitnessLetters2SingleLineLocations.getDomain().contains(wal);
	}
	
	public boolean isCompatible(ILocation loc, WitnessAutomatonLetter wal) {
		return m_SingleLineLocation2WitnessLetters.containsPair(loc, wal);
	}
	
	public Set<ILocation> getCorrespondingLocations(WitnessAutomatonLetter wal) {
		return m_WitnessLetters2SingleLineLocations.getImage(wal);
	}


	private void partitionEdges(Set<WitnessAutomatonLetter> internalAlphabet) {
		for (WitnessAutomatonLetter wal : internalAlphabet) {
			if (wal.isPureAssumptionEdge()) {
				m_PureAnnotationEdges.add(wal);
			} else {
				int lineNumber = wal.getLineNumber();
				m_LineNumber2WitnessLetter.addPair(lineNumber, wal);
			}
			
		}
	}
	
	private void matchLocations(Set<CodeBlock> internalAlphabet) {
		for (CodeBlock cb : internalAlphabet) {
			matchLocations(cb);
		}
		
	}
	
	
	private void matchLocations(CodeBlock cb) {
		if (cb instanceof Call) {
			Call call = (Call) cb;
			matchLocations(call);
		} else if (cb instanceof InterproceduralSequentialComposition) {
			InterproceduralSequentialComposition isc = (InterproceduralSequentialComposition) cb;
			matchLocations(isc);
		} else if (cb instanceof ParallelComposition) {
			ParallelComposition pc = (ParallelComposition) cb;
			matchLocations(pc);
		} else if (cb instanceof Return) {
			Return ret = (Return) cb;
			matchLocations(ret);
		} else if (cb instanceof SequentialComposition) {
			SequentialComposition sc = (SequentialComposition) cb;
			matchLocations(sc);
		} else if (cb instanceof StatementSequence) {
			StatementSequence ss = (StatementSequence) cb;
			matchLocations(ss);
		} else if (cb instanceof Summary) {
			Summary sum = (Summary) cb;
			matchLocations(sum.getCallStatement());
		} else {
			throw new AssertionError("unknown type of CodeBlock");
		}
	}

	
	private void matchLocations(Call call) {
		matchLocations(call.getCallStatement());
	}
	
	private void matchLocations(InterproceduralSequentialComposition isc) {
		for (CodeBlock cb : isc.getCodeBlocks()) {
			matchLocations(cb);
		}
	}
	


	private void matchLocations(ParallelComposition pc) {
		for (CodeBlock cb : pc.getCodeBlocks()) {
			matchLocations(cb);
		}
	}
	
	private void matchLocations(Return ret) {
		matchLocations(ret.getPayload().getLocation());
	}
	
	private void matchLocations(SequentialComposition sc) {
		for (CodeBlock cb : sc.getCodeBlocks()) {
			matchLocations(cb);
		}
	}
	
	private void matchLocations(StatementSequence ss) {
		for (Statement st : ss.getStatements()) {
			matchLocations(st);
		}
	}



	private void matchLocations(Statement st) {
		matchLocations(st.getLocation());
	}



	private void matchLocations(ILocation location) {
		if (location.getStartLine() == location.getEndLine()) {
			Set<WitnessAutomatonLetter> witnessLetters = m_LineNumber2WitnessLetter.getImage(location.getStartLine());
			if (witnessLetters != null) {
				for (WitnessAutomatonLetter wal : witnessLetters) {
					m_SingleLineLocation2WitnessLetters.addPair(location, wal);
					m_WitnessLetters2SingleLineLocations.addPair(wal, location);
				}
			}
		} else {
			m_MultiLineLocations.add(location);
		}
	}
	
	

}
