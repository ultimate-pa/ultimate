package de.uni_freiburg.informatik.ultimate.PEATestTransformer;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * Description of all meta information of the SUT that is not derivable from the requirements.
 * - Variable sets Input and Output
 * TODO: Types of variables for additional check if the types were inferred correctly from the requirements
 * @author Langenfeld
 *
 */
public class SystemInformation {
	
	private ILogger logger;
	
	//input and output variables of the System 
	private HashSet<String> inputVariables = new HashSet<>();
	private HashSet<String> outputVariables = new HashSet<>();
	private HashSet<String> internalVariables = new HashSet<>();
	private HashMap<String, String> systemVariables = new HashMap<>();
	//information which test to conduct
	//TODO:private TestInformation 
	
	//TODO: initial assignment for variables
	
	public SystemInformation(ILogger logger){
		this.logger = logger;
	}
	
	public void addInputVariable(String ident, String type){
		logger.info("Variable added as Input: " + ident + " as " + type);
		this.inputVariables.add(ident);
		this.systemVariables.put(ident, type);
	}
	
	public void addOutputVariable(String ident, String type){
		logger.info("Variable added as Output: " + ident + " as " + type);
		this.outputVariables.add(ident);
		this.systemVariables.put(ident, type);
	}
	
	public void addInternalVariable(String ident, String type){
		logger.info("Variable added as Internal: " + ident + " as " + type);
		this.internalVariables.add(ident);
		this.systemVariables.put(ident, type);
	}
	
	
	public boolean isInput(String ident) {
		return this.inputVariables.contains(ident);
	}
	
	public boolean isOutput(String ident) {
		return this.outputVariables.contains(ident);
	}
	
	public boolean isInternal(String ident) {
		return !this.isInput(ident) && !this.isOutput(ident);
	}
	
	public String getTypeOf(String ident){
		if (this.systemVariables.containsKey(ident)){
			return this.systemVariables.get(ident);
		} else {
			throw new RuntimeException("System Variable " + ident + " does not exist!");
		}
	}
	
	public Set<String> getVariableList(){
		return this.systemVariables.keySet();
	}
	
	/**
	 * Returns for a variable name a predicate of the variables initial value. 
	 * @TODO: this currently returns mockup values dependig on the type of the vairable e.g. false for boools, 0 for integers, 0.0 for floats. ... 
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

	public boolean isSystemVariable(String ident) {
		return this.systemVariables.keySet().contains(ident);
	}

	public Set<String> getInputs() {
		return this.inputVariables;
	}
	
	

}
