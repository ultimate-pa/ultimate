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

import java.util.Collections;
import java.util.List;

import de.uni_muenster.cs.sev.lethal.script.exceptions.ScriptRuntimeError;

/**
 * Raw script method. Encapsulates a procedure that can be invoked with arguments in a given Env.
 * It does NOT contain a definition environment.
 * A raw method will run when execute is called.
 * thus a some "obj.myMethod" statement will run myMethod without arguments in an env above obj. 
 * @author Philipp
 *
 */
abstract class Method extends ScriptObject{
	
	public static final int ARITY_ARBITARY = -1;
	public static final int ARITY_ZERO_OR_ONE = -2;
	public static final int ARITY_ONE_OR_TWO = -3;
	
	public static final Environment methodInstEnvt = null; // new Environment(null);
	
	private final int arity;
	
	public Method(int arity){
		super(methodInstEnvt);
		this.arity = arity;
	}
	
	/**
	 * Runs the Method without arguments in the given env.
	 * @param env object in which context this method is executed in
	 * @return result value of the method
	 */
	@Override
	public ScriptObject execute(Environment env){
		return execute(env, Collections.<ScriptObject>emptyList(), null);
		
	}
	
	/**
	 * Runs the Method with the given arguments in the given env.
	 * @param env object in which context this method is executed in
	 * @param args evaluated method arguments
	 * @param block block passed to this method, null if no block has been passed
	 * @return result value of the method
	 */
	public abstract ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block);

	public boolean checkArity(int numargs){
		if (this.arity >= 0) return arity == numargs;
		if (this.arity == ARITY_ZERO_OR_ONE) return numargs == 0 || numargs == 1;
		if (this.arity == ARITY_ONE_OR_TWO) return numargs == 1 || numargs == 2;
		return true;
	}
	
	public int getArity(){
		return this.arity;
	}
	
	public String getArityString(){
		if (this.arity >= 0) return String.valueOf(arity);
		if (this.arity == ARITY_ONE_OR_TWO) return "1 or 2";
		return "arbitary";
	}
	
	@Override
	public String toString(){
		return "Method";
	}
}

/**
 * Class for method objects. @see MethodObject
 * @author Philipp
 *
 */
class MethodClass extends ScriptClass{

	public static final MethodClass methodClass = new MethodClass();
	
	public MethodClass() {
		super("Method", null, RootClass.newStaticClassEnvironment(), false);
	}

	@Override
	public ScriptObject newInstance(List<ScriptObject> args, MethodObject block) {
		return null;
	}
	
}

/**
 * An Object wrapping a method for use outside the use as object member.
 * Whenever a method is not used as an object member (e.g. when created with proc{} or retrieved with obj.method("name"))
 * It is wrapped in an MethodObject that saves the definition env of the method and executed it in this env.
 * Additionally it changed the execute behavior. To allow MethodObject to be passed around a MethodObject will
 * return itself when execute is called not execute like raw methods do. To call a method wraped in a MethodObject
 * the MethodObject provides a "call" method as a member that will behave like the wrapped method.
 * @author Philipp
 *
 */
class MethodObject extends ScriptObject{
	
	private Method method;
	private Environment definitionEnvironment;
	
	public MethodObject(Environment definitionEnvironment, Method method){
		super(MethodClass.methodClass);
		this.definitionEnvironment = definitionEnvironment;
		this.method = method;
		
		this.setMember("call", new Method(method.getArity()){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				return MethodObject.this.method.execute(MethodObject.this.definitionEnvironment.newFrame(), args, block);
			}
		});
	}
	
	public boolean checkArity(int numargs){
		return this.method.checkArity(numargs);
	}
	public String getArityString(){
		return this.method.getArityString();
	}
	public int getArity(){
		return this.method.getArity();
	}
	
	@Override
	public ScriptObject execute(Environment env){
		return this;
	}
	
	public ScriptObject call(List<ScriptObject> args, MethodObject block){
		return this.method.execute(this.definitionEnvironment.newFrame(), args, block);
	}
	
}


/**
 * Raw User method. Subclass of methods that executes a list of user entered statements when invoked.
 * This does NOT contain a definiton environment
 * @author Philipp
 *
 */
class UserMethod extends Method {

	protected List<String> argNames;
	private List<Statement> statements;
	private boolean catchReturn;
	
	public UserMethod(List<String> argNames, List<Statement> statements, boolean catchReturn) {
		super(argNames.size());
		this.argNames = argNames;
		this.statements = statements;
		this.catchReturn = catchReturn;
	}
	
	public List<String> getArgNames(){
		return argNames;
	}

	@Override
	public ScriptObject execute(Environment env, List<ScriptObject> args, final MethodObject block) { 
		ScriptObject ret = ScriptObject.nullValue;
		for (int i = 0; i < this.argNames.size(); i++){
			env.bindLocal(argNames.get(i), args.get(i));
		}
		if (block != null){
			env.bindLocal("yield", new Method(block.getArity()){
				@Override
				public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject blockblock) {
					return block.call(args, blockblock);
				}
			});
		}
		
		env.bindLocal("block_given?", ScriptObject.make(block != null));
		
		try{
			for (Statement stmt : this.statements){
				ret = stmt.execute(env);
			}
			return ret;
		} catch (Return.ReturnException ex){
			if (this.catchReturn) {
				return ex.getReturnValue();
			} else {
				throw ex;
			}
		} catch (Break.BreakException ex){
			throw new ScriptRuntimeError("Beeak outside loop"); 
		}
	}
	
}

/**
 * An anonymous method definition statement.
 * It is created by the parser when a proc{} statement is found.
 * When executed it creates a MethodObject warping a Method with the environment this definition is executed in (definition environment)
 * @author Philipp
 *
 */
class MethodDefinition extends Expression{

	private Method method;

	public MethodDefinition(Method method) {
		this.method = method;
	}
	
	@Override
	public ScriptObject execute(Environment env) {
		return new MethodObject(env, method);
	}
	
}

/**
 * Named Method definition
 * Created by the parser when a "def" statement is found.
 * When executed it will create a MethodObject warping a Method with the environment this definition is executed in (definition environment)
 * Additionally it will bind the (raw) method to the environment it is executed in (the defining class). 
 * @author Philipp
 *
 */
class ObjectMethodBinding extends Statement{

	private Method method;
	private String name;
	
	public ObjectMethodBinding(Method method, String name) {
		this.method = method;
		this.name = name;
	}
	
	@Override
	public ScriptObject execute(Environment env) {
		env.bindLocal(this.name,this.method);
		return null;
	}
}
