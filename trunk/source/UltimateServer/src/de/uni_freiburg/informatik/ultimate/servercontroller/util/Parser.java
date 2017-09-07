package de.uni_freiburg.informatik.ultimate.servercontroller.util;

import org.apache.commons.cli.ParseException;

@FunctionalInterface
public interface Parser<In, Out> {
	public Out parse(In input) throws ParseException, java.text.ParseException;
}