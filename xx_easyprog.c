 #include <stdlib.h>

int f(int x) {
    int i = 0;

    i = i + 1;
    return  i + x;
}


int main() {
    int a = 0;
    int b = f(a);
    return b;
}

//git diff --cached --name-only --diff-filter=ACM | grep -E '\.(ml|mli)$' | xargs -I {} ocp-indent -i {}