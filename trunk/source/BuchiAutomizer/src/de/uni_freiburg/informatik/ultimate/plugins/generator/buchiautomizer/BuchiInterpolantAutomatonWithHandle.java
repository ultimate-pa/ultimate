package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;

import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.GetHandle;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.EdgeChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;

public class BuchiInterpolantAutomatonWithHandle extends
		BuchiInterpolantAutomaton {
	
	private NestedRun<CodeBlock, IPredicate> m_Handle;
	private int m_Position = 0;
	
	
	

	public BuchiInterpolantAutomatonWithHandle(SmtManager smtManager,
			EdgeChecker edgeChecker, boolean emptyStem, IPredicate precondition,
			Set<IPredicate> stemInterpolants, IPredicate hondaPredicate,
			Set<IPredicate> loopInterpolants, CodeBlock hondaEntererStem,
			CodeBlock hondaEntererLoop,
			INestedWordAutomaton<CodeBlock, IPredicate> abstraction,
			boolean scroogeNondeterminismStem,
			boolean scroogeNondeterminismLoop, boolean hondaBouncerStem,
			boolean hondaBouncerLoop, PredicateFactory predicateFactory, Logger logger, IUltimateServiceProvider  services) {
		super(smtManager, edgeChecker, emptyStem, precondition, stemInterpolants,
				hondaPredicate, loopInterpolants, hondaEntererStem,
				hondaEntererLoop, abstraction, scroogeNondeterminismStem,
				scroogeNondeterminismLoop, hondaBouncerStem, hondaBouncerLoop,  	predicateFactory ,logger, services);
		GetHandle<CodeBlock, IPredicate> gh;
		try {
			gh = new GetHandle<CodeBlock, IPredicate>(abstraction);
			m_Handle = gh.getResult();
		} catch (OperationCanceledException e) {
			throw new AssertionError();
		}
	}



	@Override
	protected boolean mayEnterHondaFromStem(CodeBlock letter) {
		if (m_Handle != null && m_Position < m_Handle.getLength() - 1) {
			assert letter.equals(m_Handle.getWord().getSymbolAt(m_Position));
			m_Position++;
			return false;
		} else {
			return super.mayEnterHondaFromStem(letter);
		}
	}
	
	

}
