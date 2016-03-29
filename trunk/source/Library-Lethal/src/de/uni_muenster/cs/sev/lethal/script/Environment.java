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

import de.uni_muenster.cs.sev.lethal.script.exceptions.ScriptRuntimeError;

import java.util.HashMap;
import java.util.Set;

/**
 * Binding table for names to their values.
 * Every environment has a pointer to it's parent env to look up values there if they are not bound localy
 * @author Philipp
 *
 */
public class Environment {

	private Environment parent;
	private HashMap<String,ScriptObject> bindings = new HashMap<String,ScriptObject>();
	private ScriptObject owner;
	
	/**
	 * New Environmnt instance
	 * @param parent parent env of this environment.
	 */
	Environment(Environment parent){
		this.parent = parent;
	}
	
	/**
	 * returns the parent environment
   * @return the parent environment
   */
	public Environment getParent(){
		return this.parent;
	}
	
	/**
	 * creates and returns a new environment on top of this one.
	 * @return new environment on top of this one
	 */
	public Environment newFrame(){
		return new Environment(this);
	}
	
	/**
	 * Reads the value for the given name from this environment.
	 * If the value is not found the parent environments will be
	 * searched recursively and the first match is returned.
	 * If no match is found an UndefinedNameException is thrown. 
	 * @param name Name of the variable to read.
	 * @return the value of the variable.
	 * @throws UndefinedNameException if no match for the given name is found.
	 */
	public ScriptObject get(String name) throws UndefinedNameException{
		ScriptObject ret = this.bindings.get(name);
		if (ret == null && this.parent != null) ret = this.parent.get(name); 
		if (ret == null) throw new UndefinedNameException(name);
		
		return ret;
	}
	
	/**
	 * Like get() but only returns a value if the given name is bound to a Method.
	 * @param name name of the method to fetch
	 * @return the method bound to the given name .
	 * @throws UndefinedNameException if no match for the given name is found.
	 * @throws ScriptRuntimeError if the match for the given name is not a method.
	 */
	public Method getMethod(String name)  throws UndefinedNameException, ScriptRuntimeError{
		ScriptObject ret = get(name);
		if (!(ret instanceof Method)) throw new ScriptRuntimeError("'" + name + "' is not a method");
		return (Method)ret;
	}
	
	/**
	 * Reads the value for the given name from this environment.
	 * If no match is found an UndefinedNameException is thrown. 
	 * @param name Name of the variable to read.
	 * @return the value of the variable.
	 * @throws UndefinedNameException if no match for the given name is found.
	 */
	public ScriptObject getLocal(String name) throws UndefinedNameException{
		ScriptObject ret = this.bindings.get(name);
		if (ret == null) throw new UndefinedNameException(name);
		return ret;
	}
	
	/**
	 * Sets a new value for the given name in the first environment it is found in.
	 * If the name is not found, a new binding will be created in this environment.
	 * @param name Name to set a value for.
	 * @param value value to set.
	 */
	public void set(String name, ScriptObject value){
		assert(name != null);
		assert(value != null);
		Environment env = findEnv(name);
		if (env == null){ // new name, bind it in the current env.
			this.bindings.put(name, value);
		} else { //know name, change the value where the innermost definition is.
			env.bindLocal(name, value);
		}	
	}
	
	/**
	 * Updates the value for the given name in THIS environment.
	 * If the name is not bound in this environment, an UndefinedNameException is thrown.
	 * @param name name to change the value for.
	 * @param value new value to set.
	* @throws UndefinedNameException thrown if the name is not locally bound
	 */
	public void putLocal(String name, ScriptObject value) throws UndefinedNameException{
		assert(name != null);
		assert(value != null);
		if (this.bindings.containsKey(name)){
			this.bindings.put(name, value);
		} else {
			throw new UndefinedNameException(name);
		}
	}
	
	/**
	 * Updates the value of or creates a new binding for the given name in THIS environment.
	 * @param name name to set the value for.
	 * @param value new value to set.
	 * @return value
	 */
	public ScriptObject bindLocal(String name, ScriptObject value){
		this.bindings.put(name, value);
		return value;
	}
	
	/**
	 * Looks up the environment where a given name is bound in
	 * @param name name to search for
	 * @return the env where the name is bound, of null if it is not found 
	 */
	private Environment findEnv(String name){
		if (this.bindings.containsKey(name)){
			return this;
		} else if (this.parent != null){
			return this.parent.findEnv(name);
		} else {
			return null;
		}
	}

	/**
	 * Returns a set of all names locally bound in this environment.
	 * @return a set of all names locally bound in this environment.
	 */
	public Set<String> getLocalMembers(){
		return this.bindings.keySet();
	}
	
	/**
	 * Sets the owner object of this Environment.
	 * It binds "this" to the owner object
	 * This is called in the ScriptObject and ScriptClass constructor automatically setting the owner of the object and class envs 
	 * @param owner the owner object of this Environment.
	 */
	public void setOwner(ScriptObject owner){
		this.owner = owner;
		this.bindings.put("this", owner);
	}
	
	/**
	 * returns the owner of this env.
	 * This is similar to getThis or get("this") but it does not recurse into parent envs.
	 * This is equivalent to calling getLocal("this") 
	 * @return the owner of this env.
	 */
	public ScriptObject getOwner(){
		return this.owner;
	}
	
	/**
	 * returns the owner of this or any parent env (first non-null owner found)
	 * @return the owner of this or any parent env (first non-null owner found)
	 */
	public ScriptObject getThis(){
		if (this.owner != null)  return this.owner;
		if (this.parent != null) return this.parent.getThis();
		return null;
	}

	
}
/**
 * Thrown if a lookup for a unbound name is performed
 * @author Philipp
 *
 */
class UndefinedNameException extends ScriptRuntimeError{
	public UndefinedNameException(String name){
		super("Undefined name '" + name + "'");
	}
}
