EXE := Frolic
EVALFILE := net1.nnue

SOURCES := Frolic.cpp

CXX := clang++

CXXFLAGS := -O3 -march=native -static -pthread -DEUNNfile=\"$(EVALFILE)\"

SUFFIX := .exe

OUT := $(EXE)$(SUFFIX)


$(EXE): $(SOURCES)
	$(CXX) $^ $(CXXFLAGS) -o $(OUT)