/*
 * Copyright (C) 2026 Manuel Bentele
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify it under the
 * terms of the GNU Lesser General Public License as published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License along with the ULTIMATE
 * CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7: If you modify the ULTIMATE CACSL2BoogieTranslator plug-in,
 * or any covered work, by linking or combining it with Eclipse RCP (or a modified version of Eclipse RCP), containing
 * parts covered by the terms of the Eclipse Public License, the licensors of the ULTIMATE CACSL2BoogieTranslator
 * plug-in grant you additional permission to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps.irq;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

/**
 * Manages interrupt requests (IRQs).
 *
 * @author Manuel Bentele
 */
public class InterruptRequestHandler {

	private final Map<Integer, InterruptRequest> mIrqs;

	private int mIrqFreeNum;

	public InterruptRequestHandler() {
		mIrqs = new HashMap<>();
		mIrqFreeNum = 1;
	}

	public boolean register(final String name) {
		return register(name, mIrqFreeNum);
	}

	public boolean register(final String name, final int num) {
		final boolean containsIrq = mIrqs.values().stream().anyMatch(irq -> irq.getName().equals(name));

		if (!containsIrq) {
			mIrqs.putIfAbsent(num, new InterruptRequest(name, mIrqFreeNum));
			mIrqFreeNum += 1;
		}

		return true;
	}

	public List<InterruptRequest> getIrqs() {
		return mIrqs.values().stream().collect(Collectors.toList());
	}

	public boolean hasIrq(final InterruptRequest irq) {
		return getIrqs().contains(irq);
	}

	public InterruptRequest getIrq(final String name) {
		return mIrqs.values().stream().filter(irq -> irq.getName().equals(name)).findFirst().orElse(null);
	}

	public InterruptRequest getIrq(final int num) {
		return mIrqs.getOrDefault(num, null);
	}

	public boolean hasIrq(final String name) {
		return (getIrq(name) != null) ? true : false;
	}

	public boolean hasIrq(final int num) {
		return mIrqs.containsKey(num);
	}

}
