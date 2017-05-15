package de.uni_freiburg.informatik.ultimate.interactive.commondata;

import java.util.List;
import java.util.function.Function;

public class ChoiceRequest<T> {
	public List<T> mChoices;
	public String mTitle;
	public String mSubTitle;
	public Function<T, String> mToString;
	
	public ChoiceRequest<T> setTitle(final String title) {
		mTitle = title;
		return this;
	}

	public ChoiceRequest<T> setSubtitle(final String subtitle) {
		mSubTitle = subtitle;
		return this;
	}

	public static <T> ChoiceRequest<T> get(final List<T> choices) {
		return get(choices, Object::toString);
	}

	public static <T> ChoiceRequest<T> get(final List<T> choices, final Function<T, String> toString) {
		final ChoiceRequest<T> result= new ChoiceRequest<>();
		result.mChoices = choices;
		result.mToString = toString;
		return result;
	};
}
