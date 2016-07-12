package de.uni_freiburg.informatik.ultimate.PEATestTransformer;

import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * Description of all meta information of the SUT that is not derivable from the reauirements.
 * - Variable sets Input and Output
 * TODO: Types of variables for additional check if the types were infered correctly from the requirements
 * @author Langenfeld
 *
 */
public class SystemInformation {
	
	//input and output variables of the System 
	private HashSet<String> inputVariables = new HashSet<String>();
	private HashSet<String> outputVariables = new HashSet<String>();
	//information which test to conduct
	//TODO:private TestInformation 
	
	//TODO: initial assignment for variables
	
	public void addInputVariable(String ident){
		this.inputVariables.add(ident);
	}
	
	public void addOutputVariable(String ident){
		this.outputVariables.add(ident);
	}
	
	
	//TODO: this is a hack and should really check if the variable is not in the inputs
	public boolean isInput(String ident) {
		return ident.startsWith("I");
	}
	//TODO: this is a hack and should really check if the variable is not in the inputs
	public boolean isOutput(String ident) {
		return ident.startsWith("O");
	}
	
	public boolean isInternal(String ident) {
		return !this.isInput(ident) && !this.isOutput(ident);
	}
	
	/**
	 * Returns for a variable name a predicate of the variables initial value. 
	 * @TODO: this currently reutns mockup values dependig on the type of the vairable e.g. false for boools, 0 for integers, 0.0 for floats. ... 
	 * @param Name
	 * @return
	 */
	public Expression getInitialAssignmentPredicate(String ident){
		ILocation loc = BoogieAstSnippet.createDummyLocation();
		return new BinaryExpression(loc,
									BinaryExpression.Operator.COMPEQ, 
									new IdentifierExpression(loc, ident), 
									new BooleanLiteral(loc, false));
	}
	
	

}
