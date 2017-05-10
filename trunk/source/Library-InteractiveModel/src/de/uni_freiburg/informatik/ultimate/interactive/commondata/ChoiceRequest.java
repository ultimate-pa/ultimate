package de.uni_freiburg.informatik.ultimate.interactive.commondata;

import java.util.List;
import java.util.function.Function;

public class ChoiceRequest<T> {
	public List<T> mChoices;
	public Function<T, String> mToString;

	public static <T> ChoiceRequest get(final List<T> choices) {
		return get(choices, Object::toString);
	}

	public static <T> ChoiceRequest get(final List<T> choices, final Function<T, String> toString) {
		final ChoiceRequest<T> result= new ChoiceRequest<>();
		result.mChoices = choices;
		result.mToString = toString;
		return result;
	};
}
