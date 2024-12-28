/** 
 * Overview:
 * 
 * Notes:
 * ASCII table used to initialize letters in efficient way, best idea I ever had
*/

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Observable;
import java.util.Random;

/**
 * 
 * @author Aurora
 */

public class WordleModel extends Observable implements IWordleModel{
    private final int LETTER_A_ASCII_VALUE = 97, LETTER_Z_ASCII_VALUE = 122;
    private HashMap<Character,Integer> availableLetters;
    private int guessStateColors[];
    private final List<String> targetWordsList;
    private final List<String> guessWordList;
    
    private String guessWord;
    private String answer;
    private int currentGuessTimes;
    private boolean isPlayerWon;
    private boolean isGuessSubmitted;
    private boolean allowNewGame;
    private boolean hasNewGameStarted;
    private boolean wordNotInList;
    private boolean displayAnswer;
    
    // 3 Flags
    private boolean onlyAllowWordListGuesses;
    private boolean alwaysDisplayAnswer;
    private boolean setRandomGuessWord;

    //@invariant invariant()
    public WordleModel(){
        targetWordsList = loadInFromFile("src/data/common.txt");
        guessWordList = loadInFromFile("src/data/words.txt");
        onlyAllowWordListGuesses = true;
        alwaysDisplayAnswer = true;
        setRandomGuessWord = true;
        wordNotInList = false;
        guessStateColors = new int[MAX_GUESSWORD_LENGTH];
        initGame();
    }

    //@ensures \result == (guess.length() <= MAX_GUESS_LENGTH && isInsideAlphabet)
    public boolean invariant(){
        boolean isInsideAlphabet = true;
        for(int i = 0; i < guessWord.length(); i++)
            if(guessWord.charAt(i) <= LETTER_A_ASCII_VALUE &&
                    guessWord.charAt(i) >= LETTER_Z_ASCII_VALUE)
                isInsideAlphabet = false;
                
        return guessWord.length() <= MAX_GUESSWORD_LENGTH && isInsideAlphabet;
    }
    /**
     * @post. All variables need to have the current values
     * at all times
     */
    public void initGame(){
        //String oldAnswer = answer;
        initAvailableLetters();
        answer = getRandomWord();
        guessWord = new String();
        
        currentGuessTimes = 0;
        isPlayerWon = false;
        isGuessSubmitted = false;
        allowNewGame = false;
        hasNewGameStarted = true;
        displayAnswer = false;
        
        setChanged();
        notifyObservers();
        // After updating Observers, set back to false
        hasNewGameStarted = false;
        //assert answer.compareTo(oldAnswer) == 1 : " No new random word generated ";
        assert currentGuessTimes == 0 : "currentGuessTry is not 0";
        assert isPlayerWon == false : "isPlayerWon is true";
        assert isGuessSubmitted == false : "isGuessSubmitted is true";
        assert allowNewGame == false : "allowNewGame is true";
        assert hasNewGameStarted == false : "hasNewGameStarted is true";
        assert displayAnswer == false : "displayAnswer is true";
    }
        
    // Getter & Setters
    public boolean alwaysShowAnswer() {return alwaysDisplayAnswer;}
    public boolean onlyWordListGuesses() {return onlyAllowWordListGuesses;}
    public boolean isGuessSubmitted() {return isGuessSubmitted;}
    public boolean displayAnwser() {return displayAnswer;}
    public boolean hasPlayerWon() {return isPlayerWon;}
    public boolean allowNewGame() {return allowNewGame;}
    public boolean hasNewGameStarted() {return hasNewGameStarted;}
    public boolean isWordNotInList() {return wordNotInList;}
    public boolean isShowAnswer() {return displayAnswer;}
    public String getAnswer() {return answer;}
    public String getGuessWord() {return guessWord;}
    public int getGuessStateColor(int index) {return guessStateColors[index];}
    public int getCurrentGuessTimes() {return currentGuessTimes;}
    public HashMap<Character,Integer> getAvailableLetters() {return availableLetters;}
    
    public void setOnlyAllowWordListGuesses(boolean con){this.onlyAllowWordListGuesses = con;}
    public void setIsGuessSubmitted(boolean isGuessSubmitted) {this.isGuessSubmitted = isGuessSubmitted;}
    /**
    * @pre. invariant must be met
    */
    public void setGuessWord(String guessWord) {
        assert invariant() : "Invariant must be true initially";
        this.guessWord = guessWord;
    }
   
    
    // Conditions
    public boolean isGuessComplete(){
        return guessWord.length() == MAX_GUESSWORD_LENGTH;
    }
    public boolean playerHasTriesLeft(){
        return currentGuessTimes != MAX_GUESS_TIMES;
    }
    
    // Methods
   
    /**
     * @pre. keyText length needs to be 1
     * @post. guess length needs to be modified with 
     * correct value and meet invariant
     */
    public void addToGuess(String keyText){
        assert keyText != null : "KeyText must exist";
        assert keyText.length() == 1 : "KeyText length needs to be 1";
        assert invariant() : "Invariant must be true initially";
        String oldGuess = guessWord;
        
        keyText = keyText.toLowerCase();
        guessWord += keyText;
        setChanged();
        notifyObservers();
        
        assert !guessWord.equals(oldGuess): "Guess not modified";
        assert guessWord.equals(oldGuess+keyText) : "Guess has been assigned wrong value";
        assert invariant() : "Invariant must be maintained";
    }

    //@requires guess != null && invariant()
    //@ensures guess.equals(removeLastChar(\old(guess))) && invariant()
    public void removeFromGuess(){
        assert guessWord != null : "Guess is null";
        String oldGuess = guessWord;
        
        guessWord = removeLastChar(guessWord);
        setChanged();
        notifyObservers();
        
        assert guessWord.length() >= 0 : "Guess is empty";
        assert !guessWord.equals(oldGuess): "guess not modified";
        assert guessWord.equals(removeLastChar(oldGuess)) : "guess has not been removed properly";
        assert invariant() : "invariant must be maintained";
    }

    //@ensures invariant() && guess.equals("") && currentGuessTry == 0
    public void submitGuess(){ 
        int oldCurrentGuessTry = currentGuessTimes;
        setChanged();
        guessWord = guessWord.toLowerCase();
        wordNotInList = false;
        if (onlyAllowWordListGuesses){
            if (!isGuessInWordList(guessWord)){
                wordNotInList = true;
                notifyObservers();
                return;
            }
        }
            
        isGuessSubmitted = true;
        colorLettersInGuess(guessWord);

        if (guessWord.equals(answer)){
            isPlayerWon = true;
        }
        
        currentGuessTimes++;
        guessWord = "";
       
        // Below checks needs to be done after try is incremented
        if (currentGuessTimes == MAX_GUESS_TIMES){
            displayAnswer = true;
        }
        // condition below not needed as guessTry is always 1,
        // but prevents variable reassignment
        if (currentGuessTimes == 1){
            allowNewGame = true;
        }
        notifyObservers();
        isGuessSubmitted = false;
        assert  isGuessSubmitted == false : "Guess not submitted.";
        assert guessWord.length() == 0 : "Guess is not empty.";
        assert currentGuessTimes == oldCurrentGuessTry + 1 :
        "CurrentGuessTry not increased." ;
    }

    //@requires guess != null
    //@ensures \result == (guessWordList.contains(guess) || targetWordsList.contains(guess))
    private boolean isGuessInWordList(String guess){
        return guessWordList.contains(guess) || targetWordsList.contains(guess); 
    }
    
    private void resetGuessStateColors(){
        Arrays.fill(guessStateColors, NO_STATE);   
    }
    
    private void colorLettersInGuess(String guess) {
        boolean[] isAnswerCharChecked = new boolean[MAX_GUESSWORD_LENGTH];
        Arrays.fill(isAnswerCharChecked, false);
        resetGuessStateColors();
        char guessChar;
        char answerChar;
        
        // Set Color to Grey
        for (int i = 0; i < MAX_GUESSWORD_LENGTH; i++){
             guessChar = guess.charAt(i);
             guessStateColors[i] = GREY_STATE;
             availableLetters.replace(guessChar, GREY_STATE);
        }
        // Set Color to Green
        for (int i = 0; i < MAX_GUESSWORD_LENGTH; i++){
            guessChar = guess.charAt(i);
            answerChar = getAnswer().charAt(i);
            if (guessChar == answerChar){
                guessStateColors[i] = GREEN_STATE;
                availableLetters.replace(guessChar, GREEN_STATE);
                isAnswerCharChecked[i] = true;
            }
        }
        // Set Color to Yellow
        for (int i = 0; i < MAX_GUESSWORD_LENGTH; i++){
            guessChar = guess.charAt(i);
            if (guessStateColors[i] != GREEN_STATE && 
                    isCharInAnswer(guessChar, isAnswerCharChecked)){
                guessStateColors[i] = YELLOW_STATE;
                if (availableLetters.get(guessChar) != GREEN_STATE)
                    availableLetters.replace(guessChar, YELLOW_STATE);
            }
        }
    }
    
    private boolean isCharInAnswer(char guessChar, boolean[] isAnswerCharChecked){
        for (int j = 0; j < MAX_GUESSWORD_LENGTH; j++){
            if (guessChar == getAnswer().charAt(j) && isAnswerCharChecked[j] == false ){
                isAnswerCharChecked[j] = true;
                return true;
            }
        }
        return false;
    }
    
    /** Initializes new memory each game, but doesn't affect performance*/
    private void initAvailableLetters() {
        availableLetters = new HashMap<>();
        for (int asciiValue = LETTER_A_ASCII_VALUE; asciiValue <= LETTER_Z_ASCII_VALUE; asciiValue++)
            availableLetters.put((char)asciiValue, NO_STATE);
    }
    
    private String getRandomWord(){
        if (!setRandomGuessWord)
            return targetWordsList.get(0);
        String word;
        Random rand = new Random(); 
        int listSize = targetWordsList.size();
        int randomIndex = rand.nextInt(listSize);
        word = targetWordsList.get(randomIndex);
        if (word.isEmpty())
            return null;
        return word;
    }
    

    private static List<String> loadInFromFile(String filePath) {
       List<String> list = new ArrayList<>();
       try {
            File file = new File(filePath);
            BufferedReader reader = new BufferedReader(new FileReader(file));
            String strLine;
            while ((strLine = reader.readLine()) != null) {
                list.add(strLine);
            }
            reader.close();
        } 
        catch (Exception e) {
            e.printStackTrace();  
        }
        return list;
    }
    
    private static String removeLastChar(String s) {
        return (s == null || s.length() == 0)
          ? null 
          : (s.substring(0, s.length() - 1));
    }
  
}
