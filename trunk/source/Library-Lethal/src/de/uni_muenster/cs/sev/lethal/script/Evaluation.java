/*
 * Copyright 2009 Dorothea Jansen <d.jansen@uni-muenster.de>, Martin Mohr <mohrfrosch@uni-muenster.de>, Irene Thesing <i_thes01@uni-muenster.de>, Anton Reis <antonreis@gmx.de>, Maria Schatz <m_scha17@uni-muenster.de>, Philipp Claves <philipp.claves@uni-muenster.de>, Sezar Jarrous <sezar.jarrous@gmail.com>
 *
 * This file is part of LETHAL.
 *
 * LETHAL is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * LETHAL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with LETHAL.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_muenster.cs.sev.lethal.script;

import java.util.ArrayList;
import java.util.List;

import de.uni_muenster.cs.sev.lethal.script.exceptions.ScriptRuntimeError;

/**
 * Expression evaluation statement.
 * Executes the expression bound to a name in the env of a source expression.
 * @author Philipp
 *
 */
public class Evaluation extends Expression {

	protected Expression sourceExp;
	protected String name;
	
	/**
	 * Create a Evaluation expression.
	 * @param name name of the expression to execute
	 * @param sourceExp expression which will yield to the object in which env "name" will be looked up and evaluated.
	 */
	public Evaluation(Expression sourceExp, String name) {
		this.sourceExp = sourceExp;
		this.name = name;
	}

	protected Environment getSourceEnv(Environment currentEnv){
		Environment sourceEnv;
		if (this.sourceExp != null){ 
			sourceEnv = this.sourceExp.execute(currentEnv).getEnvironment(); //source expression is given, name lookup and eval will happen in the env of the object the source exp evaluates to.
		} else {
			sourceEnv = currentEnv;
		}		
		return sourceEnv;
	}
	
	@Override
	public ScriptObject execute(Environment env) {
		Environment sourceEnv = getSourceEnv(env);
		ScriptObject objToExecute = sourceEnv.get(this.name);
		
		//We run the method in an frame above the object it is defined in.
		//Not a frame above the calling frame, otherwise env's for recursive calls would stack above each other and influence each others values.
		Environment execEnv = sourceEnv.getThis().newLocalEnvironment();
		
		return objToExecute.execute(execEnv.newFrame());
	}
	
	/**
	 * Update the value for the name references by this Evaluation
	 * Used when this Evaluation expression turns out to be actually on the left side of an assignment.
	 * @param env Environment this is executed in.
	 * @param newValue new value to bind.
	 */
	public void write(Environment env, ScriptObject newValue){
		if (this.sourceExp != null){
			ScriptObject val = sourceExp.execute(env);
			val.setMember(this.name, newValue); //explicit object given, write to its env, don't touch binding in parent env's.
		} else {
			env.set(this.name, newValue);
		}
	}

}


/**
 * Method Call expression
 * @author Philipp
 *
 */
class Call extends Evaluation {

	private List<Expression> args;
	private MethodDefinition blockDefinition; //block to be passed to the called method
	
	public Call(Expression sourceExp, String name, List<Expression> args, MethodDefinition blockDefinition){
		super(sourceExp,name);
		this.args = args;
		this.blockDefinition = blockDefinition;
		
	}
	
	@Override
	public ScriptObject execute(Environment env) {
		
		ScriptObject methodValue;
		Method method;
		
		Environment sourceEnv = getSourceEnv(env);
		
		methodValue = sourceEnv.get(this.name);
		if (!(methodValue instanceof Method)) throw new ScriptRuntimeError("Method or Block expected");
		method = (Method)methodValue;
		
		if (! method.checkArity(this.args.size())) throw new ScriptRuntimeError("Call " + this.name + " exptected arity " + method.getArityString() + " got " + this.args.size());
		
		//Evaluate Parameters in the current environment
		List<ScriptObject> argValues = new ArrayList<ScriptObject>(this.args.size());
		for (Expression arg : this.args){
			argValues.add(arg.execute(env));
		}
		
		
		//We run the method in an frame above the object it is defined in.
		//Not a frame above the calling frame, otherwise env's for recursive calls would stack above each other and influence each others values.
		Environment execEnv = sourceEnv.getThis().newLocalEnvironment();
		
		//Invoke method in the exec object environment.
		return method.execute(execEnv, argValues, (this.blockDefinition != null ? (MethodObject)this.blockDefinition.execute(env) : null) );
	}

}
