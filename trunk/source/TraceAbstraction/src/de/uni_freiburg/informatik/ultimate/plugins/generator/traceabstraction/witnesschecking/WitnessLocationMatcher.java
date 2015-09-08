/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 * 
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.witnesschecking;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
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
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessEdge;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessEdgeAnnotation;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessNode;

public class WitnessLocationMatcher {

	private final IUltimateServiceProvider m_Services;
	private final Set<WitnessEdge> m_PureAnnotationEdges = new HashSet<WitnessEdge>();
	private final HashRelation<Integer, WitnessEdge> m_LineNumber2WitnessLetter = new HashRelation<>();
	private final HashRelation<ILocation, WitnessEdge> m_SingleLineLocation2WitnessLetters = new HashRelation<>();
	private final HashRelation<WitnessEdge, ILocation> m_WitnessLetters2SingleLineLocations = new HashRelation<>();
	private final Set<ILocation> m_MultiLineLocations = new HashSet<ILocation>();
	private final Logger m_Logger;
	private ArrayList<WitnessEdge> m_UnmatchedWitnessLetters;

	public WitnessLocationMatcher(
			IUltimateServiceProvider services,
			INestedWordAutomatonSimple<CodeBlock, IPredicate> controlFlowAutomaton,
			NestedWordAutomaton<WitnessEdge, WitnessNode> witnessAutomaton) {
		m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
		partitionEdges(witnessAutomaton.getInternalAlphabet());
		matchLocations(controlFlowAutomaton.getInternalAlphabet());
		matchLocations(controlFlowAutomaton.getCallAlphabet());
		matchLocations(controlFlowAutomaton.getReturnAlphabet());
		m_UnmatchedWitnessLetters = new ArrayList<WitnessEdge>(witnessAutomaton.getInternalAlphabet());
		m_UnmatchedWitnessLetters.removeAll(m_WitnessLetters2SingleLineLocations.getDomain());
		m_Logger.info(witnessAutomaton.getInternalAlphabet().size() + " witness edges");
		m_Logger.info(m_PureAnnotationEdges.size() + " pure annotation edges");
		m_Logger.info(m_UnmatchedWitnessLetters.size() + " unmatched witness edges");
		m_Logger.info(m_WitnessLetters2SingleLineLocations.getDomain().size() + " matched witness edges");
		m_Logger.info(m_SingleLineLocation2WitnessLetters.getDomain().size() + " single line locations");
		m_Logger.info(m_MultiLineLocations.size() + " multi line locations");
	}

	public boolean isMatchedWitnessEdge(WitnessEdge wal) {
		return m_WitnessLetters2SingleLineLocations.getDomain().contains(wal);
	}
	
	public boolean isCompatible(ILocation loc, WitnessEdge wal) {
		return m_SingleLineLocation2WitnessLetters.containsPair(loc, wal);
	}
	
	public Set<ILocation> getCorrespondingLocations(WitnessEdge wal) {
		return m_WitnessLetters2SingleLineLocations.getImage(wal);
	}

	private void partitionEdges(Set<WitnessEdge> internalAlphabet) {
		for (WitnessEdge we : internalAlphabet) {
			int startline = we.getLocation().getStartLine();
			m_LineNumber2WitnessLetter.addPair(startline, we);
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
		if (st instanceof AssumeStatement) {
			matchLocations(((AssumeStatement) st).getFormula().getLocation());
		} else {
			matchLocations(st.getLocation());
		}
	}



	private void matchLocations(ILocation location) {
		if (location.getStartLine() == location.getEndLine()) {
			Set<WitnessEdge> witnessLetters = m_LineNumber2WitnessLetter.getImage(location.getStartLine());
			if (witnessLetters != null) {
				for (WitnessEdge wal : witnessLetters) {
					m_SingleLineLocation2WitnessLetters.addPair(location, wal);
					m_WitnessLetters2SingleLineLocations.addPair(wal, location);
				}
			}
		} else {
			m_MultiLineLocations.add(location);
		}
	}
	
	

}
