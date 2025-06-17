CHAPTER_DIR := ../LeanBook/Chapters

MD_DIR := src

NAMES :=  Appendix \
          Connectives \
          CurryHoward \
          Equality \
          FirstOrderLogic \
          InductiveTypes \
		  Introduction \
		  LambdaCalculus \
		  Lean \
		  Numbers \
		  PropositionalLogic \
		  Relations \
		  SUMMARY \
		  Tactics

MD_FILES := $(foreach item,$(NAMES), $(MD_DIR)/$(item).md)

NAT_NAMES := Intro Definition Properties
NAT_FILES := $(foreach item,$(NAT_NAMES), $(MD_DIR)/Naturals/$(item).md)

INT_NAMES := Intro Definition Properties Operators
INT_FILES := $(foreach item,$(INT_NAMES), $(MD_DIR)/Integers/$(item).md)

REAL_NAMES := Intro Dedekind Add Subtract Multiply Max Distributivity
REAL_FILES := $(foreach item,$(REAL_NAMES), $(MD_DIR)/Reals/$(item).md)

ORD_NAMES := Definition Properties Nats Sets Information Strings Maps Completions 
ORD_FILES := $(foreach item,$(ORD_NAMES), $(MD_DIR)/Ordering/$(item).md)

all: $(MD_FILES) $(NAT_FILES) $(INT_FILES) $(ORD_FILES) $(REAL_FILES)

$(MD_DIR)/%.md: $(CHAPTER_DIR)/%.lean 
	python3 dm.py $(CHAPTER_DIR)/$*.lean > $@

$(MD_DIR)/Naturals/%.md: $(CHAPTER_DIR)/Naturals/%.lean 
	python3 dm.py $(CHAPTER_DIR)/Naturals/$*.lean > $@	

$(MD_DIR)/Ordering/%.md: $(CHAPTER_DIR)/Ordering/%.lean 
	python3 dm.py $(CHAPTER_DIR)/Ordering/$*.lean > $@	

$(MD_DIR)/Reals/%.md: $(CHAPTER_DIR)/Reals/%.lean 
	python3 dm.py $(CHAPTER_DIR)/Reals/$*.lean > $@			

deploy:
	rm -rf ../docs
	cp -r book ../docs

clean:
	rm -f $(MD_DIR)/*.md \
	      $(MD_DIR)/Naturals/*.md \
		  $(MD_DIR)/Integers/*.md \
		  $(MD_DIR)/Ordering/*.md \
		  $(MD_DIR)/Reals/*.md


