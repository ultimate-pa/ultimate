package de.uni_freiburg.informatik.ultimate.PEATestTransformer;

import java.util.HashSet;

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
		return ident.startsWith("I:");
	}
	
	

}
