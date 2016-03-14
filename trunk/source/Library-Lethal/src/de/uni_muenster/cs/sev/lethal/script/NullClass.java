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
 * Class of the "null" expression
 * @author Philipp
 *
 */
public final class NullClass extends ScriptClass {
	
	/** Singleton NullClass class instance */
	public static final NullClass nullClass = new NullClass();
	
	private NullClass() {
		super("NullClass", null, RootClass.newStaticClassEnvironment(), false);
	}

	@Override
	public ScriptObject newInstance(List<ScriptObject> args, MethodObject block) {
		assert(false);
		return NullObject.nullObject;
	}

}

/**
 * Script "null" Object 
 * @author Philipp
 *
 */
class NullObject extends ScriptObject {

	public static final NullObject nullObject = new NullObject();
	
	protected NullObject() {
		super(NullClass.nullClass);
		this.getEnvironment().bindLocal("==", new Method(1){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				return ScriptObject.make(args.get(0) instanceof NullObject);
			}
		});
		this.getEnvironment().bindLocal("to_s", new Method(0){
			@Override
			public ScriptObject execute(Environment env, List<ScriptObject> args, MethodObject block) {
				return ScriptObject.make("");
			}
		});
	}
	
	@Override
	public boolean isTrue() {
		return false;
	}
	
	@Override
	public String toString(){
		return "null";
	}
	
	@Override
	public boolean equals(Object o){
		return o == nullObject;
	}
	
	@Override
	public int hashCode(){
		return 0;
	}
	
}
