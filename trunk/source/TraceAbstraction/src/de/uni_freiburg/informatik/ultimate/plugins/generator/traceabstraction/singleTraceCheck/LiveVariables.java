package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CfgBuilder.GotoEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.NestedSsaBuilder.VariableVersioneer;

/**
 * TODO: documentation
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class LiveVariables extends NestedSsaBuilder {
	private Collection<Term>[] m_ConstantsForEachPosition;
	private Set<Term>[] m_LiveConstants;
	private Set<Term>[] m_ForwardLiveConstants;
	private Set<Term>[] m_BackwardLiveConstants;
	private Set<BoogieVar>[] m_LiveVariables;
	
	public LiveVariables(NestedWord<CodeBlock> trace,
			SmtManager smtManager,
			DefaultTransFormulas defaultTransFormulas) {
		super(trace, smtManager, defaultTransFormulas);
		computeLiveVariables();
	}
	
	


	@Override
	protected void buildSSA() {
		// Initialize members
		m_ConstantsForEachPosition = new Collection[m_Formulas.getTrace().length() + 2];
		m_LiveConstants = new Set[m_ConstantsForEachPosition.length];
		m_ForwardLiveConstants = new Set[m_ConstantsForEachPosition.length];
		m_BackwardLiveConstants = new Set[m_ConstantsForEachPosition.length];
		m_LiveVariables = new Set[m_ConstantsForEachPosition.length];
		throw new UnsupportedOperationException();
	
	}




	private void computeLiveVariables() {
		computeForwardLiveConstants();
		computeBackwardLiveConstants();
		assert m_LiveConstants != null;
		// Compute live constants using forward live constants and backward live constants.
		for (int i = 0; i < m_ConstantsForEachPosition.length; i++) {
			assert m_LiveConstants[i] == null : "Live constants already computed!";
			m_ForwardLiveConstants[i].retainAll(m_BackwardLiveConstants[i]);
			m_LiveConstants[i] = m_ForwardLiveConstants[i];
		}
		
		generateLiveVariablesFromLiveConstants();
	}
	
	private void generateLiveVariablesFromLiveConstants() {
		assert m_LiveVariables != null;
		m_LiveVariables[0] = new HashSet<BoogieVar>();
		for (int i = 1; i < m_ConstantsForEachPosition.length; i++) {
			Set<BoogieVar> liveVars = new HashSet<BoogieVar>();
			for (Term t : m_LiveConstants[i]) {
				liveVars.add(m_Constants2BoogieVar.get(t));
			}
			m_LiveVariables[i] = liveVars;
		}
	}

		
	private void computeForwardLiveConstants() {
		assert m_ForwardLiveConstants != null;
		assert m_ConstantsForEachPosition != null;
		m_ForwardLiveConstants[0] = new HashSet<Term>();
		for (int i = 1; i < m_ConstantsForEachPosition.length; i++) {
			Set<Term> flc = new HashSet<Term>();
			assert m_ForwardLiveConstants[i-1] != null;
			flc.addAll(m_ForwardLiveConstants[i-1]);
			flc.addAll(m_ConstantsForEachPosition[i]);
			m_ForwardLiveConstants[i] = flc;
		}
	}
	
	private void computeBackwardLiveConstants() {
		assert m_BackwardLiveConstants != null;
		m_BackwardLiveConstants[m_ConstantsForEachPosition.length - 1] = 
				new HashSet<Term>();
		for (int i = m_ConstantsForEachPosition.length - 2; i >= 0; i--) {
			Set<Term> blc = new HashSet<Term>();
			assert m_BackwardLiveConstants[i+1] != null;
			blc.addAll(m_BackwardLiveConstants[i+1]);
			blc.addAll(m_ConstantsForEachPosition[i]);
			m_BackwardLiveConstants[i] = blc;
		}
		
	}




	
	private boolean assertLiveVariablesHasBeenComputed() {
		for (int i = 0; i < m_ConstantsForEachPosition.length; i++) {
			assert m_LiveVariables[i] != null : "LiveVariables at position " + i + " has not been computed!";
		}
		return true;
	}
	
	public Set<BoogieVar>[] getLiveVariables() {
		assert m_LiveVariables != null;
		assert assertLiveVariablesHasBeenComputed();
		return m_LiveVariables;
	}
	


}
