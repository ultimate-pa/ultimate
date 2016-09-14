/*
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE SpaceExParser plug-in.
 * 
 * The ULTIMATE SpaceExParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE SpaceExParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE SpaceExParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE SpaceExParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE SpaceExParser plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.hybridsystem;

import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.generated.BindType;

public class SystemBind {
	
	private final BindType mBind;
	private final String mBindName;
	private final ILogger mLogger;

	private final Map<String, String> mVariableMap;
	private final Map<String, Double> mConstantMap;
	
	private final double mXPosition;
	private final double mYPosition;

	protected SystemBind(final BindType bind, final ILogger logger) {
		mBind = bind;
		mBindName = bind.getAs();
		mLogger = logger;
		
		mVariableMap = new HashMap<>();
		mConstantMap = new HashMap<>();

		mXPosition = bind.getX();
		mYPosition = bind.getY();

		for (final BindType.Map map : bind.getMap()) {

			final String key = map.getKey();
			final String value = map.getValue();

			try {
				final Double parsedValue = Double.parseDouble(value);
				mConstantMap.put(key, parsedValue);
			} catch (final NumberFormatException nfe) {
				// The value is not a valid number, it must be a mapping to another variable
				mVariableMap.put(key, value);
			}
		}
	}
	
	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		
		sb.append("Bind:\n");
		sb.append("Component \"").append(mBind.getComponent()).append("\" --> \"").append(mBindName).append(":\"\n");
		sb.append("Variable map:\n");
		for (final Entry<String, String> entry : mVariableMap.entrySet()) {
			sb.append("   ").append(entry.getKey()).append(" --> ").append(entry.getValue()).append("\n");
		}
		sb.append("Constant map:\n");
		for (final Entry<String, Double> entry : mConstantMap.entrySet()) {
			sb.append("   ").append(entry.getKey()).append(" --> ").append(entry.getValue()).append("\n");
		}
		
		return sb.toString();
	}
}
