package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.witnesschecking;

import java.util.ArrayDeque;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessEdge;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessNode;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessNodeAnnotation;

public class WitnessModelToAutomatonTransformer {
	private final IUltimateServiceProvider m_Services;
	private final NestedWordAutomaton<WitnessEdge, WitnessNode> m_Result;
	private final WitnessNode m_WitnessRoot;
	private final ArrayDeque<WitnessNode> worklist = new ArrayDeque<WitnessNode>();
	
	
	
	
	public WitnessModelToAutomatonTransformer(WitnessNode witnessRoot, IUltimateServiceProvider services) {
		super();
		m_WitnessRoot = witnessRoot;
		m_Services = services;
		
		Set<WitnessEdge> internalAlphabet = new LinkedHashSet<WitnessEdge>();
		Set<WitnessEdge> callAlphabet = Collections.emptySet();
		Set<WitnessEdge> returnAlphabet = Collections.emptySet();
		StateFactory<WitnessNode> stateFactory = new StateFactory<WitnessNode>() {
		};
		m_Result = new NestedWordAutomaton<WitnessEdge, WitnessNode>(services, internalAlphabet, callAlphabet, returnAlphabet, stateFactory);
		constructAutomaton(internalAlphabet);
	}

	private void constructAutomaton(Set<WitnessEdge> internalAlphabet) {
		addNewState(m_WitnessRoot);
		while (!worklist.isEmpty()) {
			WitnessNode current = worklist.removeFirst();
			for (WitnessEdge we : current.getOutgoingEdges()) {
				WitnessNode successor = we.getTarget();
				if (!m_Result.getStates().contains(successor)) {
					addNewState(successor);
				}
				internalAlphabet.add(we);
				m_Result.addInternalTransition(current, we, successor);
			}
		}
	}

	private void addNewState(WitnessNode successor) {
		WitnessNodeAnnotation annotation = WitnessNodeAnnotation.getAnnotation(successor);
		boolean isInitial = (annotation != null && annotation.isInitial());
		boolean isFinal = (annotation != null && annotation.isError());
		m_Result.addState(isInitial, isFinal, successor);
		worklist.add(successor);
	}

	public NestedWordAutomaton<WitnessEdge, WitnessNode> getResult() {
		return m_Result;
	}
	
}
