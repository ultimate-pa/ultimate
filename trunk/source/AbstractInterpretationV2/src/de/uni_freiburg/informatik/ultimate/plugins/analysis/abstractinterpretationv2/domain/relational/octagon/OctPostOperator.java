package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgStatementExtractor;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

public class OctPostOperator implements IAbstractPostOperator<OctagonDomainState, CodeBlock, IBoogieVar> {

	private final Logger mLogger;
	private final RcfgStatementExtractor mStatementExtractor;
	private final OctStatementProcessor mStatementProcessor;

	public OctPostOperator(Logger logger, BoogieSymbolTable symbolTable) {
		mLogger = logger;
		mStatementExtractor = new RcfgStatementExtractor();
		mStatementProcessor = new OctStatementProcessor(mLogger, symbolTable);
	}

	@Override
	public OctagonDomainState apply(OctagonDomainState oldState, CodeBlock codeBlock) {
		OctagonDomainState currentState = oldState;
		for (Statement statement : mStatementExtractor.process(codeBlock)) {
			currentState = join(mStatementProcessor.process(currentState, statement));
		}
		return currentState;
	}
	
	private OctagonDomainState join(List<OctagonDomainState> states) {
		assert states.size() > 0 : "nothing to join";
		OctagonDomainState joinedState = null;
		for (OctagonDomainState result : states) {
			if (joinedState == null) {
				joinedState = result;
			} else {
				joinedState = joinedState.join(result);
			}
		}
		return joinedState;
	}

}
