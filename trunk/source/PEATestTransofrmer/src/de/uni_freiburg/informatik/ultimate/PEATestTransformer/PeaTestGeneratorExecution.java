package de.uni_freiburg.informatik.ultimate.PEATestTransformer;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.result.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.result.model.IProgramExecution;

public class PeaTestGeneratorExecution implements IProgramExecution<BoogieASTNode, Expression> {
	
	private List<ProgramState<Expression>> states;
	private SystemInformation sysInfo;
	
	public PeaTestGeneratorExecution(List<ProgramState<Expression>> states, SystemInformation sysInfo){
		this.sysInfo = sysInfo;
		this.states = states;
	}
	
	@Override
	public String toString() {
		StringBuilder out = new StringBuilder();
		//for each state makes a list of variables
		out.append("####################################### Test Sequence ###############################################\n");
		for(int i = 1; i < this.states.size() ; i++){
			out.append("-------------------------------- Step ------------------------------------------------------\n");
			out.append(this.stateChanges(this.states.get(i-1), this.states.get(i)));
			out.append("\n");
		}
		return out.toString();
	}
	
	// compare last state with next state and only print the non internal non primed variabels
	private String stateChanges(ProgramState<Expression> oldState,ProgramState<Expression> state){
		StringBuilder out = new StringBuilder("");
		String ident;
		//TODO: this loop makes variable selection hacky, make nicer!
		out.append("INPUT:");
		for(Expression variable: state.getVariables()){
			ident = ((IdentifierExpression)variable).getIdentifier();
			if(!this.sysInfo.isInput(ident)|| ident.endsWith("'")) continue;
			if(!oldState.getVariables().contains(variable) || oldState.getValues(variable) != state.getValues(variable)){
				out.append(BoogiePrettyPrinter.print(variable) +"="+ 
			BoogiePrettyPrinter.print(state.getValues(variable).stream().findFirst().get())
				+"    ");
			}
		}
		out.append("\nOUTPUT:");
		for(Expression variable: state.getVariables()){
			ident = ((IdentifierExpression)variable).getIdentifier();
			if(!this.sysInfo.isOutput(ident)|| ident.endsWith("'")) continue;
			if(!oldState.getVariables().contains(variable) || oldState.getValues(variable) != state.getValues(variable)){
				out.append(BoogiePrettyPrinter.print(variable) +"="+ 
			BoogiePrettyPrinter.print(state.getValues(variable).stream().findFirst().get())
				+"    ");
			}
		}
		out.append("\nINTERNALS:");
		for(Expression variable: state.getVariables()){
			ident = ((IdentifierExpression)variable).getIdentifier();
			if(!this.sysInfo.isInternal(ident)|| ident.endsWith("'")) continue;
			if(!oldState.getVariables().contains(variable) || oldState.getValues(variable) != state.getValues(variable)){
				out.append(BoogiePrettyPrinter.print(variable) +"="+ 
			BoogiePrettyPrinter.print(state.getValues(variable).stream().findFirst().get())
				+"    ");
			}
		}
		return out.toString();
	}

	@Override
	public int getLength() {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	public AtomicTraceElement<BoogieASTNode> getTraceElement(int index) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public ProgramState<Expression> getProgramState(
			int index) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public ProgramState<Expression> getInitialProgramState() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Class<Expression> getExpressionClass() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Class<BoogieASTNode> getTraceElementClass() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String getSVCOMPWitnessString() {
		// TODO Auto-generated method stub
		return null;
	}

}
