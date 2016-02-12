package de.uni_freiburg.informatik.ultimate.PEATestTransformer;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.DefaultTranslator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.result.model.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.result.model.IProgramExecution.ProgramState;

public class PeaTestBackTranslator extends DefaultTranslator<BoogieASTNode, BoogieASTNode, Expression, Expression> {
	
	private SystemInformation sysInfo;

	public PeaTestBackTranslator(Class<BoogieASTNode> traceElementType, Class<Expression> expressionType, SystemInformation sysInfo) {
		super(traceElementType, traceElementType, expressionType,
				expressionType);
		this.sysInfo = sysInfo; 
		//mEdgeMapping = new HashMap<>();
	}
	
	public IProgramExecution<BoogieASTNode, Expression> translateProgramExecution(
			IProgramExecution<BoogieASTNode, Expression> programExecution) {
		ProgramState<Expression> lastState = null;
		List<ProgramState<Expression>> states = new ArrayList<>();
		boolean findNextLoop = true;
		for(int i =0; i < programExecution.getLength(); i++ ){
			//programExecution.
			if(programExecution.getTraceElement(i).getTraceElement().getLocation().isLoop()){
				findNextLoop = false;
			}
			if(lastState != programExecution.getProgramState(i)){
				states.add(programExecution.getProgramState(i));
				findNextLoop = true;
			}
		}
		
		return new PeaTestGeneratorExecution(states, this.sysInfo);
	}

}
