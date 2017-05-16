package de.uni_freiburg.informatik.ultimate.interactive.commondata;

import java.util.Arrays;
import java.util.List;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ExecutionException;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.interactive.IInteractive;

public class ChoiceRequest<T> {
	public List<T> mChoices;
	public String mTitle;
	public String mSubTitle;
	public Function<T, String> mToString;
	public ILogger mLogger;

	public ChoiceRequest<T> setTitle(final String title) {
		mTitle = title;
		return this;
	}

	public ChoiceRequest<T> setLogger(final ILogger logger) {
		mLogger = logger;
		return this;
	}

	public ChoiceRequest<T> setSubtitle(final String subtitle) {
		mSubTitle = subtitle;
		return this;
	}

	public static <T> ChoiceRequest<T> get(final List<T> choices) {
		return get(choices, Object::toString);
	}

	public static <T> ChoiceRequest<T> get(final T[] choices) {
		return get(choices, Object::toString);
	}

	public static <T extends Enum<T>> ChoiceRequest<T> get(final Class<T> enumClass) {
		return get(enumClass, e -> e.name());
	}

	public static <T extends Enum<T>> ChoiceRequest<T> get(final Class<T> enumClass,
			final Function<T, String> toString) {
		return get(enumClass.getEnumConstants(), toString);
	}

	public static <T> ChoiceRequest<T> get(final T[] choices, final Function<T, String> toString) {
		return get(Arrays.asList(choices), toString);
	}

	public static <T> ChoiceRequest<T> get(final List<T> choices, final Function<T, String> toString) {
		final ChoiceRequest<T> result = new ChoiceRequest<>();
		result.mChoices = choices;
		result.mToString = toString;
		return result;
	}

	@SuppressWarnings("unchecked")
	public CompletableFuture<T> request(final IInteractive<?> interactive) {
		return interactive.common().request(Object.class, this).thenApply(o -> {
			final T result = (T) o;
			if (mLogger != null)
				mLogger.info("Client has chosen " + mToString.apply(result));
			return (T) o;
		});
	}

	public T request(final IInteractive<?> interactive, final T defaultValue) {
		try {
			final T result = request(interactive).get();
			return result;
		} catch (InterruptedException | ExecutionException e) {
			mLogger.error("Client failed to make a choice", e);
		}
		return defaultValue;
	}
}
