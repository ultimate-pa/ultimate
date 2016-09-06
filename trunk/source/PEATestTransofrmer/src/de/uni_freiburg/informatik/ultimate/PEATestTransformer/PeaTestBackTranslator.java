package de.uni_freiburg.informatik.ultimate.PEATestTransformer;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.PeaToBoogieTranslator.PEALocation;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.core.lib.translation.DefaultTranslator;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;
import pea.Phase;

public class PeaTestBackTranslator extends DefaultTranslator<BoogieASTNode, BoogieASTNode, Expression, Expression, String, String> {
	
	private SystemInformation sysInfo;

	public PeaTestBackTranslator(Class<BoogieASTNode> traceElementType, Class<Expression> expressionType, SystemInformation sysInfo, String a, String b) {
		super(traceElementType, traceElementType, expressionType,
				expressionType);
		this.sysInfo = sysInfo; 
		//mEdgeMapping = new HashMap<>();
	}
	
	@SuppressWarnings({ "deprecation", "unchecked" })
	public IProgramExecution<BoogieASTNode, Expression> translateProgramExecution(
			IProgramExecution<BoogieASTNode, Expression> programExecution) {
		ProgramState<Expression> lastState = null;
		List<ProgramState<Expression>> states = new ArrayList<>();
		List<HashSet<Phase>> phases = new ArrayList<>();
		boolean findNextLoop = true;
		HashSet<Phase> phase = new HashSet<>();

		//only report states when the loop is reentered, skip if only next codeblock
		for(int i = 0; i < programExecution.getLength(); i++ ){
			//programExecution. 
			BoogieASTNode element = programExecution.getTraceElement(i).getTraceElement();
			if(element instanceof WhileStatement){
				findNextLoop = false;
				phases.add(phase);
				phase = new HashSet<>();
			}
			
			if(lastState != programExecution.getProgramState(i) && !findNextLoop){
				ProgramState<Expression> state = programExecution.getProgramState(i);
				states.add(state);
				findNextLoop = true;
			}
			
			if(element.getLocation().getOrigin() != null
					&& element.getLocation().getOrigin() instanceof PEALocation
					&& ((PEALocation<?>)element.getLocation().getOrigin()).getElement() instanceof Phase){
						phase.add( (Phase)((PEALocation<Phase>)element.getLocation().getOrigin()).getElement() );
			}
		}
		phases.add(phase);
		phases.remove(0);
		assert(states.size() == phases.size());
		return new PeaTestGeneratorExecution(states, phases , this.sysInfo);
	}

}
