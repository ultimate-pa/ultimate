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

import java.util.List;

/**
 * Class for the Boolean data type.
 * @author Philipp
 *
 */
public class BooleanClass extends ScriptClass {

	/** Singleton BooleanClass class instance */
	public static final BooleanClass booleanClass = new BooleanClass();
	
	private BooleanClass() {
		super("Boolean", null, RootClass.newStaticClassEnvironment(), false);
	}

	@Override
	public ScriptObject newInstance(List<ScriptObject> args, MethodObject block) {
		return null;
	}

}

/**
 * Boolean object class
 * @author Philipp
 *
 */
class BooleanObject extends ScriptObject{
	
	private static final IntegerObject zero = new IntegerObject(0);
	private static final IntegerObject one = new IntegerObject(1);
	private static final Environment booleanInstEnv = FloatClass.floatClass.newInstanceEnvironment(); //one shared instance env for all integer objects. Don't need one for each of them.
	{
		booleanInstEnv.bindLocal("to_i", new Method(0){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				return (((BooleanObject)env.getThis()).getValue() ? one : zero);
			}
		});
		booleanInstEnv.setOwner(BooleanClass.booleanClass); //it is actually  an instance env, but it is shared among all instances. So we set the class as the owner.
	}
	
	private boolean value;
	
	protected BooleanObject(boolean value) {
		super(BooleanClass.booleanClass, booleanInstEnv.newFrame());
		this.value = value;
	}
	
	public boolean getValue(){
		return this.value;
	}
	
	@Override
	public boolean isTrue(){
		return this.value;
	}
	
	@Override
	public boolean equals(Object obj){
		return (obj instanceof BooleanObject && ((BooleanObject)obj).getValue() == this.value);
	}
	
	@Override
	public String toString(){
		return String.valueOf(this.value);
	}
}
