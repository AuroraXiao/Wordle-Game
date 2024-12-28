import java.util.HashMap;
/**
 *
 * @author Aurora
 */
public interface IWordleModel {
    public final int MAX_GUESS_TIMES = 6;
    public final int MAX_GUESSWORD_LENGTH = 5;
    public final int EMPTY_STATE = -2;
    public final int NO_STATE = -1, GREY_STATE = 0, GREEN_STATE = 1, YELLOW_STATE = 2;
    public boolean invariant();
    public void initGame();
    public boolean alwaysShowAnswer();
    public boolean onlyWordListGuesses();
    public boolean isGuessSubmitted();
    public boolean displayAnwser();
    public boolean hasPlayerWon();
    public boolean allowNewGame();
    public boolean hasNewGameStarted();
    public boolean isWordNotInList();
    public boolean isShowAnswer();
    public String getAnswer();
    public String getGuessWord();
    public int getGuessStateColor(int index);
    public int getCurrentGuessTimes();
    public HashMap<Character,Integer> getAvailableLetters();
    public void setOnlyAllowWordListGuesses(boolean con);
    public void setIsGuessSubmitted(boolean isGuessSubmitted);
    public void setGuessWord(String guessWord);
    public boolean isGuessComplete();
    public boolean playerHasTriesLeft();
    public void addToGuess(String keyText);
    public void removeFromGuess();
    public void submitGuess();

}
