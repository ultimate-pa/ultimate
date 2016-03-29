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

import java.util.ArrayList;
import java.util.List;

/**
 * Abstract base for all script classes
 * @author Philipp
 *
 */
public abstract class ScriptClass extends ScriptObject {
	
	private final static Method newMethod = new Method(Method.ARITY_ARBITARY){ //TODO: FIXME: get proper constructor arity
		@Override
		public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
			return ((ScriptClass)env.getThis()).newInstance(args, block);
		}
	};
	private final static Method toSMethod = new Method(0){
		@Override
		public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
			return ScriptObject.make(env.getThis().toString());
		}
	};
	private final static Method equalsOperatorMethod = new Method(1){
		@Override
		public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
			return ScriptObject.make(env.getThis().equals(args.get(0)));
		}		
	};
	private final static Method methodsMethod = new Method(0){
		@Override
		public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
			List<ScriptObject> names = new ArrayList<ScriptObject>();
			
			ScriptObject obj = env.getThis(); //get the object which methods we enumerate
			ScriptClass cls = env.getThis().getParentClass(); //and its class (if this is not already a class)
			env = obj.getEnvironment(); //we start at the env of the object (the env given as a parameter is not the same but a method exec env usually a frame above the object env). 
			
			while (env.getOwner() == obj || (cls != null && env.getOwner() == cls)){ //loop over object and class envs
				for (String name : env.getLocalMembers()){
					ScriptObject so = ScriptObject.make(name);
					if (env.get(name) instanceof Method && !names.contains(so)) names.add(so);
				}
				env = env.getParent();
			}
			return new ArrayObject(names);
		}
	};
	private final static Method membersMethod = new Method(0){
		@Override
		public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
			List<ScriptObject> names = new ArrayList<ScriptObject>();
			
			ScriptObject obj = env.getThis(); //get the object which methods we enumerate
			ScriptClass cls = env.getThis().getParentClass(); //and its class (if this is not already a class)
			env = obj.getEnvironment(); //we start at the env of the object (the env given as a parameter is not the same but a method exec env usually a frame above the object env). 

			while (env.getOwner() == obj || (cls != null && env.getOwner() == cls)){ //loop over object and class envs
				for (String name : env.getLocalMembers()){
					ScriptObject so = ScriptObject.make(name);
					if (!names.contains(so)) names.add(so);
				}
				env = env.getParent();
			}
			return new ArrayObject(names);
		}
	};
	
	private final static Method methodMethod = new Method(1){
		@Override
		public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
			if (!(args.get(0) instanceof StringObject)) throw new ScriptRuntimeError("Object.member() expects a string argument");
			return new MethodObject(env, (Method)env.getThis().getMember(((StringObject)args.get(0)).getValue()));
		}
	};
	
	
	private String className;

	/**
	 * Base constructor for new script classes
	 * @param className name of the class
	 * @param parentClass parent class (not used yet, always null so far)
	 * @param classEnvironment environment of this class (NOT the definition env, but a frame on top of it!)
	 * @param instanceable determines if the class is instanceable or not. If true the "new" constructor method will be added to the object. In this case the newInstance() method must be implemented to return a new instance object of the class. 
	 */
	public ScriptClass(String className, ScriptClass parentClass, Environment classEnvironment, boolean instanceable){
		super(classEnvironment);
		this.className = className;
		if (classEnvironment != null){
			classEnvironment.setOwner(this);
			this.setMember("class", this);
			if (instanceable) this.setMember("new", newMethod);
			this.setMember("==", equalsOperatorMethod);
			this.setMember("to_s", toSMethod);
			this.setMember("methods", methodsMethod);
			this.setMember("members", membersMethod);
			this.setMember("method", methodMethod);
		}
	}
	
	/**
	 * make a new environment for instances of this class
	 * @return a new environment for instances of this class
	 */
	public Environment newInstanceEnvironment(){
		return this.getEnvironment().newFrame();
	}
	
	/**
	 * Creates and returns a new instance of the implementing class
	 * @param args evaluated constructor parameters.
	 * @param block block passed to the constructor.
	 * @return a new instance of the class
	 */
	public abstract ScriptObject newInstance(List<ScriptObject> args, MethodObject block);
	
	@Override
	public String getClassName(){
		return this.className;
	}
	
}

/**
 * Base class for all script objects (and script classes!!)
 * Classes are also objects! 
 * @author Philipp
 *
 */
abstract class ScriptObject extends Expression{
	
	/** Global script null value */
	public static ScriptObject nullValue = NullObject.nullObject;
	/** Global script BooleanObject for false */
	public static ScriptObject falseValue = new BooleanObject(false);
	/** Global script BooleanObject for true */
	public static ScriptObject trueValue = new BooleanObject(true);

	/**
	 * Convenience method for creating an IntegerObject from an int
	 * @param value value to wrap
	 * @return the created IntegerObject
	 */
	public static IntegerObject make(int value){
		return new IntegerObject(value);
	}
	/**
	 * Convenience method for creating an FloatObject from a double value
	 * @param value value to wrap
	 * @return the created FloatObject
	 */
	public static ScriptObject make(double value){
		return new FloatObject(value);
	}
	/**
	 * Convenience method for creating an BooleanObject from a boolean value
	 * @param value value to wrap
	 * @return the created BooleanObject
	 */
	public static ScriptObject make(boolean value){
		return value ? trueValue : falseValue;
	}
	
	/**
	 * Convenience method for creating an StringObject from a String value
	 * @param value value to wrap
	 * @return the created StringObject
	 */
	public static ScriptObject make(String value){
		return new StringObject(value); 
	}
	
	/**
	 * Masks java null values.
	 * If a non-null value is given, it will be retuend without modification
	 * if a null value is given a script the NullObject will be returned instead.
	 * @param value input value
	 * @return the input value or nullValue
	 */
	public static ScriptObject maskNull(ScriptObject value){
		return (value == null) ? nullValue : value;
	}
	
	
	private final static Method isAMethod = new Method(1){
		@Override
		public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
			if (args.size() != 1 || !(args.get(0) instanceof ScriptClass)) throw new ScriptRuntimeError("kind_of?() expects a single class arguemtn");
			return ScriptObject.make(args.get(0).equals(env.getThis().parentClass)) ;
		}
	};
	private  final static Method kindOfMethod = new Method(1){
		@Override
		public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
			if (args.size() != 1 || !(args.get(0) instanceof ScriptClass)) throw new ScriptRuntimeError("kind_of?() expects a single class arguemtn");
			ScriptClass sclass = env.getThis().parentClass;
			ScriptClass refclass = (ScriptClass)args.get(0);
			while (sclass != null){
				if (sclass == refclass) return ScriptObject.trueValue;
				sclass = sclass.getParentClass();
			}
			return ScriptObject.falseValue;
		}
	};
	
	private Environment environment;
	private ScriptClass parentClass;

	/**
	 * Script object base constructor
	 * @param parentClass script class of this object
	 */
	public ScriptObject(ScriptClass parentClass){
		this(parentClass, parentClass.newInstanceEnvironment());
	}
	
	/**
	 * Script object base constructor with custom environment
	 * Used for creating primitive type instances, that don't need an individual environment for each instance
	 * @param parentClass script class of this object
	 * @param instanceEnvironment instance env of this object
	 */
	public ScriptObject(ScriptClass parentClass, Environment instanceEnvironment){
		this.environment = instanceEnvironment;
		this.parentClass = parentClass;
		
		if (this.environment != null){
			this.environment.setOwner(this);
	 		this.setMember("is_a?", isAMethod);
	 		this.setMember("kind_of?", kindOfMethod);
		}
	}

	/**
	 * Script object special constructor for use by ScriptClass constructor super() call.
	 * Should normally not be used.
	 * Does not initialize owner and common object methods.
	 * @param environment environment of this object/class
	 */
	public ScriptObject(Environment environment){
		this.environment = environment;
		this.parentClass = null;
	}

	/**
	 * Environment of this object
   * @return Environment of this object
   */
	protected Environment getEnvironment(){
		return this.environment;
	}
	
	/**
	 * Creates a new local environment frame for method running in object context.
   * @return new local environment frame for method running in object context.
   */
	public Environment newLocalEnvironment(){
		return this.environment.newFrame();
	}
	
	/**
	 * Looks up a member (aka variable) of this object in its environment
	 * XXX: it also looks in the parent env's. This is wrong but currently needed for user classes to work. FIXME!  
	 * @param name name of the member
	 * @return member with the given name.
	 * @throws UndefinedMemberException if there is no member with the given name.
	 */
	public ScriptObject getMember(String name){
		try{
			return this.environment.get(name);
		} catch (UndefinedNameException ex){
			throw new UndefinedMemberException(this, name);
		}
	}
	
	/**
	 * Same as getMember, but will also check if the given name is bound to a method.
	 * @param name the name of the method to look up
	 * @return the method bound to the name
	 */
	public Method getMethod(String name){
		try{
			return this.environment.getMethod(name);
		} catch (UndefinedNameException ex){
			throw new UndefinedMemberException(this, name);
		}
	}
	
	/**
	 * Binds a name to the given value in object context
	 * @param name name to bind to
	 * @param newValue value to bind
	 * @return newValue
	 */
	public ScriptObject setMember(String name, ScriptObject newValue){
		this.environment.bindLocal(name, newValue);
		return newValue;
	}
	/**
	 * Binds a name to the given value in object context
	 * @param name name to bind to
	 * @param newValue value to bind
	 * @return newValue
	 */
	public Method setMember(String name, Method newValue){
		this.environment.bindLocal(name, newValue);
		return newValue;
	}
	
	/**
	 * Evaluate this object. Default behavior is for objects to evaluate to itself
	 * @param env Environment to evaluate in (ignored by default)
	 * @return evaluation result (this by default) 
	 */
	@Override
	public ScriptObject execute(Environment env){
		return this;
	}
	
	/**
	 * Class of this object
	 * @return class of this object
	 */
	public ScriptClass getParentClass(){
		return this.parentClass;
	}
	
	/**
	 * Returns the name of the class of this object.
	 * @return the name of the class of this object.
	 */
	public String getClassName(){
		return this.parentClass.getClassName();
	}
	
	/**
	 * Returns if this object is considered true by script flow control statements and boolean operators. 
	 * @return true  if this object is considered true by script flow control statements and boolean operators false if not.
	 */
	public boolean isTrue() {
		return true;
	}
	
	@Override
	public String toString(){
		 return this.getClassName();
	}
}

/**
 * Thrown on read access to an unbound name
 * @author Philipp
 *
 */
class UndefinedMemberException extends ScriptRuntimeError {

	public UndefinedMemberException(ScriptObject object, String name) {
		super(object.toString() + " has no member named '" + name + "'");
	}
	
}
